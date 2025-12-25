#!/usr/bin/env python3

import os
import re
import sys
from pathlib import Path


def update_imports_in_file(file_path, import_mappings):
    """Update import statements in a single file."""
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()

        original_content = content

        # Pattern to match import statements
        # Matches: open import ModuleName
        # Also handles: import ModuleName
        import_pattern = r"^(\s*(?:open\s+)?import\s+)([A-Za-z][A-Za-z0-9.]*)"

        lines = content.split("\n")
        updated_lines = []

        for line in lines:
            updated_line = line
            match = re.match(import_pattern, line)

            if match:
                prefix = match.group(1)  # "open import " or "import "
                module_name = match.group(2)  # The actual module name

                # Check if this module needs to be updated
                if module_name in import_mappings:
                    new_module_name = import_mappings[module_name]
                    updated_line = re.sub(
                        r"^(\s*(?:open\s+)?import\s+)" + re.escape(module_name),
                        r"\1" + new_module_name,
                        line,
                    )
                    print(f"  Updated: {module_name} -> {new_module_name}")

            updated_lines.append(updated_line)

        updated_content = "\n".join(updated_lines)

        # Only write if content changed
        if updated_content != original_content:
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(updated_content)
            return True

        return False

    except Exception as e:
        print(f"Error processing {file_path}: {e}")
        return False


def main():
    # Define the mapping from old import paths to new import paths
    import_mappings = {
        # Root level modules
        "Cocontinuity": "QIT.Cocontinuity",
        "Colimit": "QIT.Colimit",
        "ContainerFunctor": "QIT.ContainerFunctor",
        "Equivalence": "QIT.Equivalence",
        "Order": "QIT.Order",
        "Plump": "QIT.Plump",
        "Prelude": "QIT.Prelude",
        "Setoid": "QIT.Setoid",
        "Subset": "QIT.Subset",
        # Mobile modules
        "Mobile.Base": "QIT.Mobile.Base",
        "Mobile.Cocontinuity": "QIT.Mobile.Cocontinuity",
        "Mobile.Colimit": "QIT.Mobile.Colimit",
        "Mobile.Equivalence": "QIT.Mobile.Equivalence",
        "Mobile.Functor": "QIT.Mobile.Functor",
        # Setoid modules
        "Setoid.Base": "QIT.Setoid.Base",
        "Setoid.Functor": "QIT.Setoid.Functor",
        "Setoid.Hom": "QIT.Setoid.Hom",
        "Setoid.Iso": "QIT.Setoid.Iso",
        "Setoid.Sigma": "QIT.Setoid.Sigma",
    }

    # Find all .agda and .lagda.md files
    project_root = Path(".")
    agda_files = list(project_root.glob("**/*.agda"))
    lagda_files = list(project_root.glob("**/*.lagda.md"))
    all_files = agda_files + lagda_files

    if not all_files:
        print("No .agda or .lagda.md files found!")
        return

    print(f"Found {len(all_files)} files to process:")
    for f in sorted(all_files):
        print(f"  {f}")
    print()

    updated_count = 0

    for file_path in sorted(all_files):
        print(f"Processing {file_path}...")
        if update_imports_in_file(file_path, import_mappings):
            updated_count += 1
            print(f"  ✓ Updated")
        else:
            print(f"  - No changes needed")
        print()

    print(f"Summary: Updated {updated_count} out of {len(all_files)} files.")

    if updated_count > 0:
        print("\nImport refactoring complete!")
        print("You should now test the build with: agda --build-library")
    else:
        print("\nNo files needed updating.")


if __name__ == "__main__":
    main()
