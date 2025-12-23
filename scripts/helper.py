#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tai-e Assignment Helper
A utility script for managing Tai-e course assignments.

Features:
- Setup dependencies (copy files from previous assignments)
- Package submission files
- Run tests
- Submit (test + package)
"""

import os
import sys
import json
import shutil
import subprocess
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple
import zipfile

# Fix Windows console encoding issues
if sys.platform == 'win32':
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')


class Colors:
    """ANSI color codes for terminal output"""
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    RESET = '\033[0m'
    BOLD = '\033[1m'

    @staticmethod
    def disable():
        """Disable colors for non-terminal output"""
        Colors.GREEN = ''
        Colors.YELLOW = ''
        Colors.RED = ''
        Colors.BLUE = ''
        Colors.CYAN = ''
        Colors.RESET = ''
        Colors.BOLD = ''


class AssignmentHelper:
    """Main class for assignment helper functionality"""

    def __init__(self, root_dir: Path):
        self.root_dir = root_dir
        self.scripts_dir = root_dir / "scripts"
        self.config_file = self.scripts_dir / "config.json"
        self.metadata_file = self.scripts_dir / "assignment_metadata.json"
        self.output_dir = root_dir / "output"

        # Check if stdout is a terminal
        if not sys.stdout.isatty():
            Colors.disable()

    def load_config(self) -> Dict:
        """Load user configuration"""
        if not self.config_file.exists():
            print(f"{Colors.YELLOW}⚠ Config file not found. Please run 'config' command first.{Colors.RESET}")
            sys.exit(1)

        with open(self.config_file, 'r', encoding='utf-8') as f:
            return json.load(f)

    def save_config(self, config: Dict):
        """Save user configuration"""
        with open(self.config_file, 'w', encoding='utf-8') as f:
            json.dump(config, f, indent=2, ensure_ascii=False)

    def load_metadata(self) -> Dict:
        """Load assignment metadata"""
        if not self.metadata_file.exists():
            print(f"{Colors.RED}✗ Metadata file not found: {self.metadata_file}{Colors.RESET}")
            print(f"  Please ensure assignment_metadata.json exists in scripts/ directory")
            sys.exit(1)

        with open(self.metadata_file, 'r', encoding='utf-8') as f:
            return json.load(f)

    def get_assignment_dir(self, assignment: str) -> Path:
        """Get assignment directory path"""
        return self.root_dir / assignment / "tai-e"

    def check_git_status(self, file_path: Path) -> Dict:
        """Check Git status of a file"""
        try:
            # Check if file is modified
            result = subprocess.run(
                ['git', 'status', '--porcelain', str(file_path)],
                cwd=self.root_dir,
                capture_output=True,
                text=True,
                timeout=5
            )

            status = result.stdout.strip()

            if not status:
                return {'status': 'unmodified'}
            elif status.startswith(' M') or status.startswith('M '):
                # Get last commit info
                log_result = subprocess.run(
                    ['git', 'log', '-1', '--format=%h|%cr|%s', '--', str(file_path)],
                    cwd=self.root_dir,
                    capture_output=True,
                    text=True,
                    timeout=5
                )

                if log_result.stdout.strip():
                    parts = log_result.stdout.strip().split('|', 2)
                    if len(parts) == 3:
                        return {
                            'status': 'modified',
                            'commit': parts[0],
                            'time': parts[1],
                            'message': parts[2]
                        }

                return {'status': 'modified'}
            elif status.startswith('??'):
                return {'status': 'untracked'}

            return {'status': 'unknown'}

        except (subprocess.SubprocessError, FileNotFoundError):
            # Git not available or not a git repo, fallback to file modification time
            if file_path.exists():
                mtime = datetime.fromtimestamp(file_path.stat().st_mtime)
                days_ago = (datetime.now() - mtime).days
                if days_ago == 0:
                    time_str = "today"
                elif days_ago == 1:
                    time_str = "yesterday"
                else:
                    time_str = f"{days_ago} days ago"

                return {'status': 'unknown', 'time': time_str}

            return {'status': 'unknown'}

    def cmd_config(self, args):
        """Configure student ID and name"""
        print(f"{Colors.BOLD}Assignment Helper Configuration{Colors.RESET}")
        print("=" * 50)

        # Load existing config if available
        existing_config = {}
        if self.config_file.exists():
            with open(self.config_file, 'r', encoding='utf-8') as f:
                existing_config = json.load(f)

        # Get student ID
        default_id = existing_config.get('student_id', '')
        prompt = f"Student ID [{default_id}]: " if default_id else "Student ID: "
        student_id = input(prompt).strip()
        if not student_id and default_id:
            student_id = default_id

        # Get student name
        default_name = existing_config.get('student_name', '')
        prompt = f"Student Name [{default_name}]: " if default_name else "Student Name: "
        student_name = input(prompt).strip()
        if not student_name and default_name:
            student_name = default_name

        if not student_id or not student_name:
            print(f"{Colors.RED}✗ Both student ID and name are required{Colors.RESET}")
            sys.exit(1)

        config = {
            'student_id': student_id,
            'student_name': student_name,
            'workspace_root': str(self.root_dir)
        }

        self.save_config(config)
        print(f"\n{Colors.GREEN}✓ Configuration saved successfully{Colors.RESET}")
        print(f"  Student ID: {student_id}")
        print(f"  Student Name: {student_name}")

    def cmd_list(self, args):
        """List all assignments"""
        metadata = self.load_metadata()

        print(f"\n{Colors.BOLD}Available Assignments{Colors.RESET}")
        print("=" * 70)

        for assignment_id in sorted(metadata.keys()):
            info = metadata[assignment_id]
            dep_count = len(info.get('dependencies', []))
            file_count = len(info.get('files_to_submit', []))

            print(f"\n{Colors.CYAN}{assignment_id}{Colors.RESET}: {info['name']}")
            print(f"  Files to submit: {file_count}")
            print(f"  Dependencies: {dep_count} file(s) from previous assignments")

            if dep_count > 0:
                deps_from = set(dep['from'] for dep in info['dependencies'])
                print(f"  Depends on: {', '.join(sorted(deps_from))}")

    def cmd_info(self, args):
        """Show detailed information about an assignment"""
        metadata = self.load_metadata()
        assignment = args.assignment

        if assignment not in metadata:
            print(f"{Colors.RED}✗ Invalid assignment: {assignment}{Colors.RESET}")
            print(f"  Valid assignments: {', '.join(sorted(metadata.keys()))}")
            sys.exit(1)

        info = metadata[assignment]

        print(f"\n{Colors.BOLD}Assignment {assignment}: {info['name']}{Colors.RESET}")
        print("=" * 70)

        # Files to submit
        print(f"\n{Colors.CYAN}Files to Submit:{Colors.RESET}")
        for file_path in info['files_to_submit']:
            print(f"  • {file_path}")

        # Dependencies
        deps = info.get('dependencies', [])
        if deps:
            print(f"\n{Colors.CYAN}Dependencies:{Colors.RESET}")
            for dep in deps:
                print(f"  • From {dep['from']}: {os.path.basename(dep['file'])}")
        else:
            print(f"\n{Colors.CYAN}Dependencies:{Colors.RESET} None")

    def cmd_setup(self, args):
        """Setup dependencies for an assignment"""
        metadata = self.load_metadata()
        assignment = args.assignment

        if assignment not in metadata:
            print(f"{Colors.RED}✗ Invalid assignment: {assignment}{Colors.RESET}")
            sys.exit(1)

        info = metadata[assignment]
        deps = info.get('dependencies', [])

        if not deps:
            print(f"{Colors.YELLOW}ℹ Assignment {assignment} has no dependencies{Colors.RESET}")
            return

        print(f"\n{Colors.BOLD}Setting up dependencies for {assignment}...{Colors.RESET}")
        print("=" * 70)

        target_dir = self.get_assignment_dir(assignment)
        success_count = 0
        skip_count = 0
        force_all = args.force

        for idx, dep in enumerate(deps, 1):
            source_assignment = dep['from']
            file_rel_path = dep['file']

            source_dir = self.get_assignment_dir(source_assignment)
            source_file = source_dir / file_rel_path
            target_file = target_dir / file_rel_path

            # Print header
            print(f"\n[{idx}/{len(deps)}] {os.path.basename(file_rel_path)}")
            print(f"  {source_assignment} → {assignment}")
            print()

            # Check source file exists
            if not source_file.exists():
                print(f"  Status: {Colors.RED}✗ Source file not found{Colors.RESET}")
                continue

            # Determine target file status
            target_exists = target_file.exists()
            git_status = self.check_git_status(target_file) if target_exists else None
            is_modified = git_status and git_status.get('status') == 'modified'

            # Display status
            if not target_exists:
                print(f"  Status: ℹ Target file does not exist")
            elif is_modified:
                time_str = git_status.get('time', 'recently')
                print(f"  Status: 📝 Target file modified {time_str}")
            else:
                print(f"  Status: ✓ Target file unchanged")

            # Handle modified files (need confirmation)
            if is_modified and not force_all:
                print(f"  {Colors.YELLOW}⚠ This will overwrite your local changes.{Colors.RESET}")
                print(f"  Options:")
                print(f"    y - Yes, overwrite this file")
                print(f"    n - No, skip this file")
                print(f"    a - All, overwrite this and all remaining files")
                print(f"    q - Quit setup")
                print(f"  Your choice [y/N/a/q]: ", end='')
                choice = input().lower().strip()

                if choice == 'q':
                    print(f"\n{Colors.YELLOW}Setup cancelled by user{Colors.RESET}")
                    sys.exit(0)
                elif choice == 'a':
                    force_all = True
                    print()
                elif choice != 'y':
                    print(f"  {Colors.YELLOW}→ Skipped{Colors.RESET}")
                    skip_count += 1
                    continue
                else:
                    print()

            # Perform copy
            try:
                target_file.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source_file, target_file)

                if is_modified and force_all:
                    print(f"  {Colors.GREEN}✓ Copied (overwrote local changes){Colors.RESET}")
                else:
                    print(f"  {Colors.GREEN}✓ Copied{Colors.RESET}")

                success_count += 1
            except Exception as e:
                print(f"  {Colors.RED}✗ Failed: {str(e)}{Colors.RESET}")

        # Summary
        print(f"\n{Colors.BOLD}Summary:{Colors.RESET}")
        print(f"  {Colors.GREEN}✓{Colors.RESET} Copied: {success_count}")
        if skip_count > 0:
            print(f"  {Colors.YELLOW}→{Colors.RESET} Skipped: {skip_count}")

    def cmd_test(self, args):
        """Run tests for an assignment"""
        assignment = args.assignment
        assignment_dir = self.get_assignment_dir(assignment)

        if not assignment_dir.exists():
            print(f"{Colors.RED}✗ Assignment directory not found: {assignment_dir}{Colors.RESET}")
            sys.exit(1)

        print(f"\n{Colors.BOLD}Running tests for {assignment}...{Colors.RESET}")
        print("=" * 70)

        # Determine gradle wrapper command
        if os.name == 'nt':  # Windows
            gradle_cmd = 'gradlew.bat'
        else:
            gradle_cmd = './gradlew'

        gradle_wrapper = assignment_dir / gradle_cmd.lstrip('./')
        if not gradle_wrapper.exists():
            print(f"{Colors.RED}✗ Gradle wrapper not found: {gradle_wrapper}{Colors.RESET}")
            sys.exit(1)

        # Run tests
        cmd = [str(gradle_wrapper), 'test', '--console=plain']
        print(f"Command: {' '.join(cmd)}")
        print(f"Working directory: {assignment_dir}\n")

        try:
            result = subprocess.run(
                cmd,
                cwd=assignment_dir,
                capture_output=not args.verbose,
                text=True
            )

            # Parse results
            test_report = assignment_dir / "build" / "reports" / "tests" / "test" / "index.html"

            if result.returncode == 0:
                print(f"\n{Colors.GREEN}{'=' * 70}{Colors.RESET}")
                print(f"{Colors.GREEN}✓ BUILD SUCCESSFUL{Colors.RESET}")
                print(f"{Colors.GREEN}{'=' * 70}{Colors.RESET}")

                if test_report.exists():
                    print(f"\nDetailed report: {test_report}")

                return True
            else:
                print(f"\n{Colors.RED}{'=' * 70}{Colors.RESET}")
                print(f"{Colors.RED}✗ BUILD FAILED{Colors.RESET}")
                print(f"{Colors.RED}{'=' * 70}{Colors.RESET}")

                if not args.verbose and result.stdout:
                    # Show last 30 lines of output
                    lines = result.stdout.split('\n')
                    print("\nLast lines of output:")
                    print('\n'.join(lines[-30:]))

                if test_report.exists():
                    print(f"\nDetailed report: {test_report}")

                return False

        except Exception as e:
            print(f"{Colors.RED}✗ Failed to run tests: {str(e)}{Colors.RESET}")
            return False

    def cmd_package(self, args):
        """Package submission files"""
        config = self.load_config()
        metadata = self.load_metadata()
        assignment = args.assignment

        if assignment not in metadata:
            print(f"{Colors.RED}✗ Invalid assignment: {assignment}{Colors.RESET}")
            sys.exit(1)

        info = metadata[assignment]
        student_id = config['student_id']
        student_name = config['student_name']

        print(f"\n{Colors.BOLD}Packaging {assignment} for submission...{Colors.RESET}")
        print("=" * 70)

        # Create output directory
        self.output_dir.mkdir(exist_ok=True)

        # Collect files
        assignment_dir = self.get_assignment_dir(assignment)
        files_to_package = []
        missing_files = []

        for file_rel_path in info['files_to_submit']:
            source_file = assignment_dir / file_rel_path
            if source_file.exists():
                files_to_package.append((source_file, file_rel_path))
                print(f"{Colors.GREEN}✓{Colors.RESET} {os.path.basename(file_rel_path)}")
            else:
                missing_files.append(file_rel_path)
                print(f"{Colors.RED}✗{Colors.RESET} {os.path.basename(file_rel_path)} (not found)")

        if missing_files:
            print(f"\n{Colors.RED}✗ Cannot package: {len(missing_files)} file(s) missing{Colors.RESET}")
            sys.exit(1)

        # Create ZIP file
        zip_filename = f"{student_id}-{student_name}-{assignment}.zip"
        zip_path = self.output_dir / zip_filename

        print(f"\nCreating archive: {zip_filename}")

        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zipf:
            for source_file, arcname in files_to_package:
                # Put files in root directory, using only filename
                zip_arcname = os.path.basename(arcname)
                zipf.write(source_file, zip_arcname)

        # Get file size
        file_size = zip_path.stat().st_size
        if file_size < 1024:
            size_str = f"{file_size} B"
        elif file_size < 1024 * 1024:
            size_str = f"{file_size / 1024:.1f} KB"
        else:
            size_str = f"{file_size / (1024 * 1024):.1f} MB"

        print(f"\n{Colors.GREEN}{'=' * 70}{Colors.RESET}")
        print(f"{Colors.GREEN}✓ Package created successfully{Colors.RESET}")
        print(f"{Colors.GREEN}{'=' * 70}{Colors.RESET}")
        print(f"\nFile: {zip_path}")
        print(f"Size: {size_str}")
        print(f"Files: {len(files_to_package)}")

    def cmd_submit(self, args):
        """Run tests and package if successful"""
        print(f"{Colors.BOLD}Submitting {args.assignment}...{Colors.RESET}")
        print("=" * 70)

        # Run tests first
        test_success = self.cmd_test(args)

        if not test_success:
            print(f"\n{Colors.RED}✗ Tests failed. Cannot package for submission.{Colors.RESET}")
            print(f"  Fix the failing tests and try again.")
            sys.exit(1)

        # Package files
        print(f"\n{Colors.BOLD}Tests passed! Proceeding with packaging...{Colors.RESET}\n")
        self.cmd_package(args)


def main():
    """Main entry point"""
    # Determine root directory
    script_dir = Path(__file__).parent
    root_dir = script_dir.parent

    helper = AssignmentHelper(root_dir)

    # Create argument parser
    parser = argparse.ArgumentParser(
        description='Tai-e Assignment Helper',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python helper.py config              # Configure student info
  python helper.py list                # List all assignments
  python helper.py info A3             # Show A3 details
  python helper.py setup A3            # Setup A3 dependencies
  python helper.py test A3             # Run A3 tests
  python helper.py package A3          # Package A3 for submission
  python helper.py submit A3           # Test + Package A3
        """
    )

    subparsers = parser.add_subparsers(dest='command', help='Available commands')

    # Config command
    subparsers.add_parser('config', help='Configure student ID and name')

    # List command
    subparsers.add_parser('list', help='List all assignments')

    # Info command
    info_parser = subparsers.add_parser('info', help='Show assignment details')
    info_parser.add_argument('assignment', help='Assignment ID (e.g., A3)')

    # Setup command
    setup_parser = subparsers.add_parser('setup', help='Setup assignment dependencies')
    setup_parser.add_argument('assignment', help='Assignment ID (e.g., A3)')
    setup_parser.add_argument('--force', action='store_true', help='Overwrite without asking')

    # Test command
    test_parser = subparsers.add_parser('test', help='Run assignment tests')
    test_parser.add_argument('assignment', help='Assignment ID (e.g., A3)')
    test_parser.add_argument('--verbose', action='store_true', help='Show full test output')

    # Package command
    package_parser = subparsers.add_parser('package', help='Package files for submission')
    package_parser.add_argument('assignment', help='Assignment ID (e.g., A3)')

    # Submit command
    submit_parser = subparsers.add_parser('submit', help='Run tests and package if successful')
    submit_parser.add_argument('assignment', help='Assignment ID (e.g., A3)')
    submit_parser.add_argument('--verbose', action='store_true', help='Show full test output')

    # Parse arguments
    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        sys.exit(1)

    # Execute command
    try:
        if args.command == 'config':
            helper.cmd_config(args)
        elif args.command == 'list':
            helper.cmd_list(args)
        elif args.command == 'info':
            helper.cmd_info(args)
        elif args.command == 'setup':
            helper.cmd_setup(args)
        elif args.command == 'test':
            helper.cmd_test(args)
        elif args.command == 'package':
            helper.cmd_package(args)
        elif args.command == 'submit':
            helper.cmd_submit(args)
    except KeyboardInterrupt:
        print(f"\n\n{Colors.YELLOW}Operation cancelled by user{Colors.RESET}")
        sys.exit(1)
    except Exception as e:
        print(f"\n{Colors.RED}✗ Error: {str(e)}{Colors.RESET}")
        if '--debug' in sys.argv:
            raise
        sys.exit(1)


if __name__ == '__main__':
    main()
