#!/usr/bin/env python3

import os
import re
import subprocess
import sys
from pathlib import Path


def fix_relation_references():
    """Fix references after relation restructure, targeting only what's broken."""

    print("Targeted Relation Fix")
    print("=" * 25)

    # Define specific fixes needed for each file
    file_fixes = {
        "QIT/Setoid/Iso.agda": [
            ("QIT.Equivalence", "QIT.Relation.Binary"),
        ],
        "QIT/Colimit.agda": [
            ("QIT.Order", "QIT.Relation.Binary"),
            ("QIT.Equivalence", "QIT.Relation.Binary"),
        ],
        "QIT/Cocontinuity.agda": [
            ("QIT.Order", "QIT.Relation.Binary"),
            ("QIT.Equivalence", "QIT.Relation.Binary"),
        ],
        "QIT/Mobile/Base.agda": [
            ("QIT.Equivalence", "QIT.Relation.Binary"),
        ],
        "QIT/Mobile/Equivalence.agda": [
            ("QIT.Equivalence", "QIT.Relation.Binary"),
        ],
        "QIT/Mobile/Functor.agda": [
            ("QIT.Equivalence", "QIT.Relation.Binary"),
        ],
        "QIT/Mobile/Cocontinuity.agda": [
            ("QIT.Equivalence", "QIT.Relation.Binary"),
            ("QIT.Plump", "QIT.Relation.Plump"),
        ],
        "QIT/Mobile/Colimit.agda": [
            ("QIT.Equivalence", "QIT.Relation.Binary"),
            ("QIT.Plump", "QIT.Relation.Plump"),
            ("QIT.Subset", "QIT.Relation.Subset"),
            ("QIT.Order", "QIT.Relation.Binary"),
        ],
        "README.lagda.md": [
            ("QIT.Equivalence", "QIT.Relation.Binary"),
            ("QIT.Order", "QIT.Relation.Binary"),
            ("QIT.Plump", "QIT.Relation.Plump"),
        ],
    }

    updated_count = 0

    for file_path_str, replacements in file_fixes.items():
        file_path = Path(file_path_str)
        if not file_path.exists():
            print(f"  Skipping {file_path} (not found)")
            continue

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            original_content = content

            # Apply import replacements
            for old_import, new_import in replacements:
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

    print(f"\nUpdated {updated_count} files")

    # Test README first
    print("\nTesting README...")
    try:
        result = subprocess.run(
            ["agda", "README.lagda.md"],
            capture_output=True,
            text=True,
            cwd=Path("."),
        )

        if result.returncode == 0:
            print("✅ README builds successfully!")

            # Test full build
            print("\nTesting full build...")
            result = subprocess.run(
                ["agda", "--build-library"],
                capture_output=True,
                text=True,
                cwd=Path("."),
            )

            if result.returncode == 0:
                print("✅ Full build successful!")
                return True
            else:
                print("❌ Full build failed:")
                print(result.stdout)
                if result.stderr:
                    print(result.stderr)
                return False
        else:
            print("❌ README build failed:")
            print(result.stdout)
            if result.stderr:
                print(result.stderr)
            return False

    except Exception as e:
        print(f"❌ Error testing: {e}")
        return False


if __name__ == "__main__":
    success = fix_relation_references()
    if success:
        print("\n🎉 Relation fixes completed successfully!")
    else:
        print("\n💥 Relation fixes encountered issues.")
    sys.exit(0 if success else 1)
