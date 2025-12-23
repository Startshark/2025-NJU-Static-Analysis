# Assignment Helper Tool

A Python utility for managing Tai-e course assignments.

## Features

- **Setup Dependencies**: Automatically copy required files from previous assignments
- **Run Tests**: Execute Gradle tests for assignments
- **Package Submissions**: Create properly formatted ZIP files for submission
- **Smart File Detection**: Git-aware file modification detection

## Quick Start

### 1. First-time Setup

```bash
# Configure your student ID and name
python scripts/helper.py config
```

### 2. Working on an Assignment

```bash
# View all assignments
python scripts/helper.py list

# View details for a specific assignment
python scripts/helper.py info A3

# Setup dependencies (copy files from previous assignments)
python scripts/helper.py setup A3

# Run tests
python scripts/helper.py test A3

# Package for submission
python scripts/helper.py package A3

# Or do everything: test + package (recommended)
python scripts/helper.py submit A3
```

## Commands

### `config`
Configure student information (ID and name).

```bash
python scripts/helper.py config
```

### `list`
List all available assignments with their dependencies.

```bash
python scripts/helper.py list
```

### `info <assignment>`
Show detailed information about a specific assignment.

```bash
python scripts/helper.py info A3
```

### `setup <assignment>`
Copy dependency files from previous assignments.

```bash
# Interactive mode (asks before overwriting modified files)
python scripts/helper.py setup A3

# Force overwrite without asking
python scripts/helper.py setup A3 --force
```

**Smart Features:**
- Detects if target files have been modified using Git
- Shows last modification time
- Prompts before overwriting modified files
- Supports batch operations with 'a' (all) option

### `test <assignment>`
Run Gradle tests for an assignment.

```bash
# Run tests with summary output
python scripts/helper.py test A3

# Run tests with full verbose output
python scripts/helper.py test A3 --verbose
```

### `package <assignment>`
Create a ZIP file for submission.

```bash
python scripts/helper.py package A3
```

Output: `output/<student_id>-<student_name>-A3.zip`

### `submit <assignment>`
Run tests and package if tests pass (recommended for final submission).

```bash
python scripts/helper.py submit A3
```

This command will:
1. Run all tests
2. Only create the ZIP package if tests pass
3. Prevent accidental submission of broken code

## File Structure

```
Tai-e-assignments/
├── scripts/
│   ├── helper.py                     # Main script
│   ├── assignment_metadata.json      # Assignment definitions
│   ├── config.json                   # Your configuration (created by 'config' command)
│   └── config.example.json           # Configuration template
├── output/                            # Generated ZIP files
├── A1/tai-e/...                       # Assignment 1
├── A2/tai-e/...                       # Assignment 2
└── ...
```

## Configuration

The `config.json` file stores your student information:

```json
{
  "student_id": "12345678",
  "student_name": "Zhang San",
  "workspace_root": "D:/Tai-e-assignments"
}
```

This file is created automatically when you run `python scripts/helper.py config`.

