#!/usr/bin/env python3

import os
import re
import subprocess
import sys
from pathlib import Path


def fix_relation_imports_simple():
    """Simple fix for relation imports after restructure."""

    print("Simple Relation Import Fix")
    print("=" * 30)

    # Map old imports to new relation-based imports
    import_mappings = {
        "QIT.Equivalence": "QIT.Relation.Binary",
        "QIT.Order": "QIT.Relation.Binary",
        "QIT.Plump": "QIT.Relation.Plump",
        "QIT.Subset": "QIT.Relation.Subset",
    }

    project_root = Path(".")
    all_files = list(project_root.glob("**/*.agda")) + list(
        project_root.glob("**/*.lagda.md")
    )

    print(f"Step 1: Updating import statements...")

    updated_count = 0
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
                updated_count += 1
                print(f"  Updated: {file_path}")

        except Exception as e:
            print(f"  Error updating {file_path}: {e}")

    print(f"Updated {updated_count} files")

    print(f"\nStep 2: Testing build...")
    try:
        result = subprocess.run(
            ["agda", "README.lagda.md"],
            capture_output=True,
            text=True,
            cwd=project_root,
        )

        if result.returncode == 0:
            print("✅ README BUILD SUCCESSFUL!")
            return True
        else:
            print("❌ README BUILD FAILED:")
            print("Error output:")
            if result.stdout:
                print(result.stdout)
            if result.stderr:
                print(result.stderr)
            return False

    except Exception as e:
        print(f"❌ ERROR running build test: {e}")
        return False


if __name__ == "__main__":
    success = fix_relation_imports_simple()
    if success:
        print("\n🎉 Simple relation import fix completed successfully!")
    else:
        print("\n💥 Import fix encountered issues.")
    sys.exit(0 if success else 1)
