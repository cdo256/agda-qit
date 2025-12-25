#!/usr/bin/env python3

import os
import re
import subprocess
import sys
from pathlib import Path


def simple_refactor():
    """Simple refactor to move all modules under QIT/ namespace."""

    print("Simple QIT Refactor Script")
    print("=" * 40)

    # Step 1: Update all import statements
    print("\nStep 1: Updating import statements...")

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

    # Update import statements only
    for file_path in all_files:
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            original_content = content

            # Update import statements (both "import X" and "open import X")
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
            print(f"  Error updating imports in {file_path}: {e}")

    # Step 2: Update module declarations
    print("\nStep 2: Updating module declarations...")

    # Map file paths to their expected module names
    module_files = [
        # Simple modules (module Name where)
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
        ("QIT/Cocontinuity.agda", "Cocontinuity", "QIT.Cocontinuity"),
        ("QIT/Colimit.agda", "Colimit", "QIT.Colimit"),
        ("QIT/ContainerFunctor.agda", "ContainerFunctor", "QIT.ContainerFunctor"),
        ("QIT/Plump.agda", "Plump", "QIT.Plump"),
        ("QIT/Setoid/Sigma.agda", "Setoid.Sigma", "QIT.Setoid.Sigma"),
    ]

    for file_path_str, old_module, new_module in module_files:
        file_path = Path(file_path_str)
        if not file_path.exists():
            continue

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            original_content = content

            # Update top-level module declaration
            # Handle both "module Name where" and "module Name(...) where"
            # This pattern matches the first occurrence of the module declaration
            pattern = (
                r"^(\s*)module\s+"
                + re.escape(old_module)
                + r"(\s*(?:\([^)]*\)|\{[^}]*\})*\s*(?:where)?)"
            )
            replacement = r"\1module " + new_module + r"\2"
            content = re.sub(pattern, replacement, content, count=1, flags=re.MULTILINE)

            if content != original_content:
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(content)
                print(f"  Updated module: {file_path}")

        except Exception as e:
            print(f"  Error updating module in {file_path}: {e}")

    # Step 3: Test the build
    print("\nStep 3: Testing build...")
    try:
        result = subprocess.run(
            ["agda", "--build-library"],
            capture_output=True,
            text=True,
            cwd=project_root,
        )

        if result.returncode == 0:
            print("✅ BUILD SUCCESSFUL!")
            print("\nRefactor completed successfully!")
            return True
        else:
            print("❌ BUILD FAILED:")
            print("STDOUT:")
            print(result.stdout)
            print("\nSTDERR:")
            print(result.stderr)
            return False

    except Exception as e:
        print(f"❌ ERROR running build test: {e}")
        return False


if __name__ == "__main__":
    success = simple_refactor()
    if success:
        print("\n🎉 Simple refactor completed successfully!")
    else:
        print("\n💥 Refactor encountered issues - see output above.")
    sys.exit(0 if success else 1)
