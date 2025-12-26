#!/usr/bin/env python3

import os
import re
import sys
from pathlib import Path


def fix_agda_files_for_qit_refactor():
    """Complete refactor to move all modules under QIT/ namespace."""

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

    # Also need to handle module references that are not imports
    module_ref_mappings = {
        "Colim": "QIT.Colimit",
    }

    project_root = Path(".")
    agda_files = list(project_root.glob("**/*.agda"))
    lagda_files = list(project_root.glob("**/*.lagda.md"))
    all_files = agda_files + lagda_files

    print(f"Processing {len(all_files)} files...")

    updated_count = 0

    for file_path in sorted(all_files):
        print(f"\nProcessing {file_path}...")

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            original_content = content
            lines = content.split("\n")
            updated_lines = []

            for line_num, line in enumerate(lines):
                updated_line = line

                # 1. Fix import statements
                import_match = re.match(
                    r"^(\s*(?:open\s+)?import\s+)([A-Za-z][A-Za-z0-9.]*)", line
                )
                if import_match:
                    prefix = import_match.group(1)
                    module_name = import_match.group(2)
                    if module_name in import_mappings:
                        new_module_name = import_mappings[module_name]
                        updated_line = re.sub(
                            r"^(\s*(?:open\s+)?import\s+)" + re.escape(module_name),
                            r"\1" + new_module_name,
                            line,
                        )
                        print(f"  Import: {module_name} -> {new_module_name}")

                # 2. Fix module declarations
                # Handle simple case: module ModuleName where
                module_match = re.match(
                    r"^(\s*)module\s+([A-Za-z][A-Za-z0-9.]*)\s+(where\s*)$", line
                )
                if module_match:
                    indent = module_match.group(1)
                    old_module_name = module_match.group(2)
                    where_clause = module_match.group(3)

                    # Determine new module name based on file path
                    if file_path.name == "README.lagda.md":
                        new_module_name = "README"
                    else:
                        # Convert path to module name
                        rel_path = file_path.relative_to(project_root)
                        path_parts = list(rel_path.parts)
                        if path_parts[-1].endswith(".agda"):
                            path_parts[-1] = path_parts[-1][:-5]
                        elif path_parts[-1].endswith(".lagda.md"):
                            path_parts[-1] = path_parts[-1][:-9]
                        new_module_name = ".".join(path_parts)

                    if old_module_name != new_module_name:
                        updated_line = (
                            f"{indent}module {new_module_name} {where_clause}"
                        )
                        print(f"  Module: {old_module_name} -> {new_module_name}")

                # 3. Fix module declarations with parameters (multi-line)
                param_module_match = re.match(
                    r"^(\s*)module\s+([A-Za-z][A-Za-z0-9.]*)\s*(\{[^}]*\}|\([^)]*\))",
                    line,
                )
                if param_module_match:
                    indent = param_module_match.group(1)
                    old_module_name = param_module_match.group(2)
                    params = param_module_match.group(3)

                    # Determine new module name based on file path
                    if file_path.name == "README.lagda.md":
                        new_module_name = "README"
                    else:
                        rel_path = file_path.relative_to(project_root)
                        path_parts = list(rel_path.parts)
                        if path_parts[-1].endswith(".agda"):
                            path_parts[-1] = path_parts[-1][:-5]
                        elif path_parts[-1].endswith(".lagda.md"):
                            path_parts[-1] = path_parts[-1][:-9]
                        new_module_name = ".".join(path_parts)

                    if old_module_name != new_module_name:
                        updated_line = f"{indent}module {new_module_name} {params}"
                        print(
                            f"  Parameterized module: {old_module_name} -> {new_module_name}"
                        )

                # 4. Fix module references (like "open Colim")
                for old_ref, new_ref in module_ref_mappings.items():
                    if re.search(r"\bopen\s+" + re.escape(old_ref) + r"\b", line):
                        updated_line = re.sub(
                            r"\bopen\s+" + re.escape(old_ref) + r"\b",
                            f"open {new_ref}",
                            updated_line,
                        )
                        print(f"  Module ref: open {old_ref} -> open {new_ref}")

                # 5. Fix local module names that conflict with top-level modules
                # Handle the specific case in Colimit.agda
                if "module QIT.Colimit(" in line and file_path.name == "Colimit.agda":
                    updated_line = line.replace("module QIT.Colimit(", "module _(")
                    print(f"  Fixed local module conflict")

                updated_lines.append(updated_line)

            updated_content = "\n".join(updated_lines)

            # Only write if content changed
            if updated_content != original_content:
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(updated_content)
                updated_count += 1
                print(f"  ✓ Updated")
            else:
                print(f"  - No changes needed")

        except Exception as e:
            print(f"  ✗ Error: {e}")

    print(f"\n" + "=" * 50)
    print(f"Summary: Updated {updated_count} out of {len(all_files)} files.")

    if updated_count > 0:
        print("\nRefactor complete! Testing build...")
        # Test the build
        import subprocess

        try:
            result = subprocess.run(
                ["agda", "--build-library"],
                capture_output=True,
                text=True,
                cwd=project_root,
            )
            if result.returncode == 0:
                print("✓ Build successful!")
            else:
                print("✗ Build failed:")
                print(result.stdout)
                print(result.stderr)
                return False
        except Exception as e:
            print(f"Could not test build: {e}")

    return True


if __name__ == "__main__":
    success = fix_agda_files_for_qit_refactor()
    sys.exit(0 if success else 1)
