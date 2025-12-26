#!/usr/bin/env python3

import os
import re
import sys
from pathlib import Path


def targeted_refactor():
    """Targeted refactor to fix the main issues with QIT/ namespace."""

    # Step 1: Update imports in all files
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

    project_root = Path(".")
    all_files = list(project_root.glob("**/*.agda")) + list(
        project_root.glob("**/*.lagda.md")
    )

    print("Step 1: Updating import statements...")

    for file_path in all_files:
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            original_content = content

            # Update import statements
            for old_import, new_import in import_mappings.items():
                # Match "import ModuleName" or "open import ModuleName"
                pattern = (
                    r"^(\s*(?:open\s+)?import\s+)" + re.escape(old_import) + r"(\s|$)"
                )
                replacement = r"\1" + new_import + r"\2"
                content = re.sub(pattern, replacement, content, flags=re.MULTILINE)

            if content != original_content:
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(content)
                print(f"  Updated imports: {file_path}")

        except Exception as e:
            print(f"  Error updating {file_path}: {e}")

    print("\nStep 2: Updating top-level module declarations...")

    # Step 2: Update only top-level module declarations
    module_files = [
        # Files with simple top-level modules
        ("QIT/Equivalence.agda", "Equivalence", "QIT.Equivalence"),
        ("QIT/Order.agda", "Order", "QIT.Order"),
        ("QIT/Prelude.agda", "Prelude", "QIT.Prelude"),
        ("QIT/Setoid.agda", "Setoid", "QIT.Setoid"),
        ("QIT/Subset.agda", "Subset", "QIT.Subset"),
        ("QIT/Setoid/Base.agda", "Setoid.Base", "QIT.Setoid.Base"),
        ("QIT/Setoid/Functor.agda", "Setoid.Functor", "QIT.Setoid.Functor"),
        ("QIT/Setoid/Hom.agda", "Setoid.Hom", "QIT.Setoid.Hom"),
        ("QIT/Setoid/Iso.agda", "Setoid.Iso", "QIT.Setoid.Iso"),
        # Parameterized modules
        ("QIT/Mobile/Base.agda", "Mobile.Base", "QIT.Mobile.Base"),
        (
            "QIT/Mobile/Cocontinuity.agda",
            "Mobile.Cocontinuity",
            "QIT.Mobile.Cocontinuity",
        ),
        ("QIT/Mobile/Colimit.agda", "Mobile.Colimit", "QIT.Mobile.Colimit"),
        ("QIT/Mobile/Equivalence.agda", "Mobile.Equivalence", "QIT.Mobile.Equivalence"),
        ("QIT/Mobile/Functor.agda", "Mobile.Functor", "QIT.Mobile.Functor"),
    ]

    for file_path_str, old_module, new_module in module_files:
        file_path = Path(file_path_str)
        if not file_path.exists():
            print(f"  Warning: {file_path} not found")
            continue

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            original_content = content

            # Update top-level module declaration (first occurrence only)
            # Handle both "module Name where" and "module Name(...) where"
            pattern = (
                r"^(\s*)module\s+"
                + re.escape(old_module)
                + r"(\s*(?:\([^)]*\)|\{[^}]*\})?\s*where)"
            )
            replacement = r"\1module " + new_module + r"\2"
            content = re.sub(pattern, replacement, content, count=1, flags=re.MULTILINE)

            if content != original_content:
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(content)
                print(f"  Updated module: {file_path}")

        except Exception as e:
            print(f"  Error updating {file_path}: {e}")

    print("\nStep 3: Handling special cases...")

    # Step 3: Handle special cases manually

    # Fix Cocontinuity.agda - parameterized module and module reference
    cocont_path = Path("QIT/Cocontinuity.agda")
    if cocont_path.exists():
        try:
            with open(cocont_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Update the top-level parameterized module
            content = re.sub(
                r"^(\s*)module\s+Cocontinuity\s*(\{[^}]*\})",
                r"\1module QIT.Cocontinuity \2",
                content,
                count=1,
                flags=re.MULTILINE,
            )

            # Update "open Colim" to "open QIT.Colimit"
            content = re.sub(r"\bopen\s+Colim\b", "open QIT.Colimit", content)

            with open(cocont_path, "w", encoding="utf-8") as f:
                f.write(content)
            print(f"  Updated special case: {cocont_path}")

        except Exception as e:
            print(f"  Error updating {cocont_path}: {e}")

    # Fix Colimit.agda - parameterized module
    colimit_path = Path("QIT/Colimit.agda")
    if colimit_path.exists():
        try:
            with open(colimit_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Update the top-level parameterized module
            content = re.sub(
                r"^(\s*)module\s+Colimit\s*(\{[^}]*\})",
                r"\1module QIT.Colimit \2",
                content,
                count=1,
                flags=re.MULTILINE,
            )

            with open(colimit_path, "w", encoding="utf-8") as f:
                f.write(content)
            print(f"  Updated special case: {colimit_path}")

        except Exception as e:
            print(f"  Error updating {colimit_path}: {e}")

    # Fix Plump.agda - parameterized module
    plump_path = Path("QIT/Plump.agda")
    if plump_path.exists():
        try:
            with open(plump_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Update the top-level parameterized module
            content = re.sub(
                r"^(\s*)module\s+Plump\s*(\{[^}]*\})",
                r"\1module QIT.Plump \2",
                content,
                count=1,
                flags=re.MULTILINE,
            )

            with open(plump_path, "w", encoding="utf-8") as f:
                f.write(content)
            print(f"  Updated special case: {plump_path}")

        except Exception as e:
            print(f"  Error updating {plump_path}: {e}")

    # Fix ContainerFunctor.agda - parameterized module
    container_path = Path("QIT/ContainerFunctor.agda")
    if container_path.exists():
        try:
            with open(container_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Update the top-level parameterized module
            content = re.sub(
                r"^(\s*)module\s+ContainerFunctor\s*(\{[^}]*\})",
                r"\1module QIT.ContainerFunctor \2",
                content,
                count=1,
                flags=re.MULTILINE,
            )

            with open(container_path, "w", encoding="utf-8") as f:
                f.write(content)
            print(f"  Updated special case: {container_path}")

        except Exception as e:
            print(f"  Error updating {container_path}: {e}")

    # Fix Setoid/Sigma.agda - parameterized module
    sigma_path = Path("QIT/Setoid/Sigma.agda")
    if sigma_path.exists():
        try:
            with open(sigma_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Update the top-level parameterized module
            content = re.sub(
                r"^(\s*)module\s+Setoid\.Sigma\s*$",
                r"\1module QIT.Setoid.Sigma",
                content,
                count=1,
                flags=re.MULTILINE,
            )

            with open(sigma_path, "w", encoding="utf-8") as f:
                f.write(content)
            print(f"  Updated special case: {sigma_path}")

        except Exception as e:
            print(f"  Error updating {sigma_path}: {e}")

    # Fix mobile modules that have "open Colim" references
    mobile_files = ["QIT/Mobile/Cocontinuity.agda", "QIT/Mobile/Colimit.agda"]
    for mobile_file in mobile_files:
        mobile_path = Path(mobile_file)
        if mobile_path.exists():
            try:
                with open(mobile_path, "r", encoding="utf-8") as f:
                    content = f.read()

                # Update "open Colim" to "open QIT.Colimit"
                original_content = content
                content = re.sub(r"\bopen\s+Colim\b", "open QIT.Colimit", content)

                if content != original_content:
                    with open(mobile_path, "w", encoding="utf-8") as f:
                        f.write(content)
                    print(f"  Updated Colim references: {mobile_path}")

            except Exception as e:
                print(f"  Error updating {mobile_path}: {e}")

    print("\nStep 4: Testing build...")

    # Test the build
    import subprocess

    try:
        result = subprocess.run(
            ["agda", "--build-library"], capture_output=True, text=True, cwd=Path(".")
        )
        if result.returncode == 0:
            print("✓ Build successful!")
            return True
        else:
            print("✗ Build failed:")
            print("STDOUT:", result.stdout)
            print("STDERR:", result.stderr)
            return False
    except Exception as e:
        print(f"Could not test build: {e}")
        return False


if __name__ == "__main__":
    success = targeted_refactor()
    print(f"\nRefactor {'completed successfully' if success else 'failed'}!")
    sys.exit(0 if success else 1)
