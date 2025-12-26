#!/usr/bin/env python3

import os
import re
import subprocess
import sys
from pathlib import Path


def fix_relation_imports():
    """Fix imports after relation modules were restructured."""

    print("Fixing Relation Import Mappings")
    print("=" * 40)

    # Map old imports to new relation-based imports
    import_mappings = {
        "QIT.Equivalence": "QIT.Relation.Binary",
        "QIT.Order": "QIT.Relation.Binary",
        "QIT.Plump": "QIT.Relation.Plump",
        "QIT.Subset": "QIT.Relation.Subset",
    }

    # Also need to update references that were using these modules
    symbol_mappings = {
        # From old QIT.Equivalence
        "Reflexive": "Reflexive",
        "Symmetric": "Symmetric",
        "Transitive": "Transitive",
        "IsEquivalence": "IsEquivalence",
        "isEquiv≡p": "isEquiv-≡p",
        # From old QIT.Order
        "WfRec": "WfRec",
        "Acc": "Acc",
        "WellFounded": "WellFounded",
        "IsPreorder": "IsPreorder",
        "Preorder": "Preorder",
        "IsWeaklyExtensional": "isWeaklyExtensional",
        # Need to handle Rel -> BinaryRel
        "Rel": "BinaryRel",
    }

    project_root = Path(".")
    all_files = list(project_root.glob("**/*.agda")) + list(
        project_root.glob("**/*.lagda.md")
    )

    print(f"\nStep 1: Updating imports in {len(all_files)} files...")

    # Update import statements
    updated_files = []
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
                updated_files.append(file_path)
                print(f"  Updated imports: {file_path}")

        except Exception as e:
            print(f"  Error updating imports in {file_path}: {e}")

    print(f"\nStep 2: Updating specific symbol references...")

    # Files that need special handling for symbol updates
    special_updates = [
        # QIT.Setoid.Base needs Rel -> BinaryRel
        ("QIT/Setoid/Base.agda", [(r"\bRel\b", "BinaryRel")]),
        # QIT.Colimit needs various updates
        (
            "QIT/Colimit.agda",
            [
                (r"\bRel\b", "BinaryRel"),
                (r"\bReflexive\b", "Reflexive"),
                (r"\bTransitive\b", "Transitive"),
                (r"\bIsPreorder\b", "IsPreorder"),
                (r"\bPreorder\b", "Preorder"),
            ],
        ),
        # Mobile files need symbol updates
        (
            "QIT/Mobile/Base.agda",
            [
                (r"\bIsEquivalence\b", "IsEquivalence"),
            ],
        ),
        (
            "QIT/Mobile/Equivalence.agda",
            [
                (r"\bIsEquivalence\b", "IsEquivalence"),
            ],
        ),
        (
            "QIT/Mobile/Functor.agda",
            [
                (r"\bIsEquivalence\b", "IsEquivalence"),
            ],
        ),
        # QIT.Setoid.Iso needs equivalence symbols
        (
            "QIT/Setoid/Iso.agda",
            [
                (r"\bIsEquivalence\b", "IsEquivalence"),
            ],
        ),
        # Cocontinuity needs preorder symbols
        (
            "QIT/Cocontinuity.agda",
            [
                (r"\bIsPreorder\b", "IsPreorder"),
                (r"\bPreorder\b", "Preorder"),
                (r"\bRel\b", "BinaryRel"),
            ],
        ),
    ]

    for file_path_str, replacements in special_updates:
        file_path = Path(file_path_str)
        if not file_path.exists():
            continue

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            original_content = content

            for old_symbol, new_symbol in replacements:
                content = re.sub(old_symbol, new_symbol, content)

            if content != original_content:
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(content)
                print(f"  Updated symbols: {file_path}")

        except Exception as e:
            print(f"  Error updating symbols in {file_path}: {e}")

    print(f"\nStep 3: Adding missing Rel definition to Prelude...")

    # The Prelude had Rel removed but other files might still expect it
    # Let's add it back as an alias to BinaryRel
    prelude_path = Path("QIT/Prelude.agda")
    if prelude_path.exists():
        try:
            with open(prelude_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Check if Rel definition is missing and BinaryRel import isn't there
            if "Rel :" not in content and "BinaryRel" not in content:
                # Add the missing import and definition
                lines = content.split("\n")

                # Find a good place to add the import - after other QIT imports
                insert_index = 0
                for i, line in enumerate(lines):
                    if line.strip().startswith("open import"):
                        insert_index = i + 1
                    elif line.strip() == "":
                        break

                # Insert the import
                lines.insert(insert_index, "open import QIT.Relation.Base")

                # Find where to add the Rel alias
                for i, line in enumerate(lines):
                    if "open Box" in line:
                        lines.insert(i + 2, "")
                        lines.insert(
                            i + 3, "Rel : ∀ (X : Set ℓ) ℓ' → Set (ℓ ⊔ lsuc ℓ')"
                        )
                        lines.insert(i + 4, "Rel X ℓ' = BinaryRel X ℓ'")
                        break

                new_content = "\n".join(lines)

                with open(prelude_path, "w", encoding="utf-8") as f:
                    f.write(new_content)
                print(f"  Updated Prelude with Rel alias")

        except Exception as e:
            print(f"  Error updating Prelude: {e}")

    print(f"\nStep 4: Testing build...")
    try:
        result = subprocess.run(
            ["agda", "README.lagda.md"],
            capture_output=True,
            text=True,
            cwd=project_root,
        )

        if result.returncode == 0:
            print("✅ README BUILD SUCCESSFUL!")

            # Try full build
            result = subprocess.run(
                ["agda", "--build-library"],
                capture_output=True,
                text=True,
                cwd=project_root,
            )

            if result.returncode == 0:
                print("✅ FULL BUILD SUCCESSFUL!")
                return True
            else:
                print("❌ FULL BUILD FAILED:")
                print("STDOUT:", result.stdout)
                print("STDERR:", result.stderr)
                return False
        else:
            print("❌ README BUILD FAILED:")
            print("STDOUT:", result.stdout)
            print("STDERR:", result.stderr)
            return False

    except Exception as e:
        print(f"❌ ERROR running build test: {e}")
        return False


if __name__ == "__main__":
    success = fix_relation_imports()
    if success:
        print("\n🎉 Relation import fixes completed successfully!")
    else:
        print("\n💥 Relation import fixes encountered issues - see output above.")
    sys.exit(0 if success else 1)
