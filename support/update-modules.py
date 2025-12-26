#!/usr/bin/env python3

import os
import re
import sys
from pathlib import Path


def update_module_declaration(file_path, new_module_name):
    """Update the module declaration in a single file."""
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()

        original_content = content

        # Pattern to match module declarations
        # Matches: module ModuleName where
        # Also handles: module ModuleName (...) where
        module_pattern = (
            r"^(\s*)module\s+([A-Za-z][A-Za-z0-9.]*)\s*(\([^)]*\))?\s+(where\s*.*)"
        )

        lines = content.split("\n")
        updated_lines = []

        for line in lines:
            updated_line = line
            match = re.match(module_pattern, line, re.DOTALL)

            if match:
                indent = match.group(1)
                old_module_name = match.group(2)
                params = match.group(3) or ""  # Parameters like (param : Type)
                where_clause = match.group(4)

                updated_line = (
                    f"{indent}module {new_module_name}{params} {where_clause}"
                )
                print(f"  Updated module: {old_module_name} -> {new_module_name}")
                break

            updated_lines.append(updated_line)

        # If we found and updated a module declaration, reconstruct the content
        if updated_line != line:
            # Replace the first line that matched
            updated_content = content.replace(line, updated_line, 1)
        else:
            updated_content = content

        # Only write if content changed
        if updated_content != original_content:
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(updated_content)
            return True

        return False

    except Exception as e:
        print(f"Error processing {file_path}: {e}")
        return False


def path_to_module_name(file_path, base_path):
    """Convert a file path to the corresponding module name."""
    # Get relative path from base
    rel_path = file_path.relative_to(base_path)

    # Remove .agda or .lagda.md extension
    path_parts = list(rel_path.parts)
    if path_parts[-1].endswith(".agda"):
        path_parts[-1] = path_parts[-1][:-5]  # Remove .agda
    elif path_parts[-1].endswith(".lagda.md"):
        path_parts[-1] = path_parts[-1][:-9]  # Remove .lagda.md

    # Join with dots to create module name
    return ".".join(path_parts)


def main():
    project_root = Path(".")

    # Find all .agda files in the QIT directory
    qit_files = list(project_root.glob("QIT/**/*.agda"))

    # Also handle README.lagda.md specially
    readme_file = project_root / "README.lagda.md"

    all_files = qit_files
    if readme_file.exists():
        all_files.append(readme_file)

    if not all_files:
        print("No files found to process!")
        return

    print(f"Found {len(all_files)} files to process:")
    for f in sorted(all_files):
        print(f"  {f}")
    print()

    updated_count = 0

    for file_path in sorted(all_files):
        print(f"Processing {file_path}...")

        if file_path.name == "README.lagda.md":
            # README should have module name "README"
            new_module_name = "README"
        else:
            # Convert path to module name
            new_module_name = path_to_module_name(file_path, project_root)

        if update_module_declaration(file_path, new_module_name):
            updated_count += 1
            print(f"  ✓ Updated")
        else:
            print(f"  - No changes needed")
        print()

    print(f"Summary: Updated {updated_count} out of {len(all_files)} files.")

    if updated_count > 0:
        print("\nModule declaration refactoring complete!")
        print("You should now test the build with: agda --build-library")
    else:
        print("\nNo files needed updating.")


if __name__ == "__main__":
    main()
