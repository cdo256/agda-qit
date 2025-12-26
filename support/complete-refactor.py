#!/usr/bin/env python3

import os
import re
import subprocess
import sys
from pathlib import Path


def complete_refactor():
    """Complete refactor to move all modules under QIT/ namespace with proper handling."""

    print("QIT Refactor Script")
    print("=" * 50)

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

    # Update imports
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
            print(f"  Error updating imports in {file_path}: {e}")

    # Step 2: Update module declarations
    print("\nStep 2: Updating module declarations...")

    module_updates = [
        # Simple modules
        ("QIT/Equivalence.agda", "module Equivalence", "module QIT.Equivalence"),
        ("QIT/Order.agda", "module Order", "module QIT.Order"),
        ("QIT/Prelude.agda", "module Prelude", "module QIT.Prelude"),
        ("QIT/Setoid.agda", "module Setoid", "module QIT.Setoid"),
        ("QIT/Subset.agda", "module Subset", "module QIT.Subset"),
        ("QIT/Setoid/Base.agda", "module Setoid.Base", "module QIT.Setoid.Base"),
        (
            "QIT/Setoid/Functor.agda",
            "module Setoid.Functor",
            "module QIT.Setoid.Functor",
        ),
        ("QIT/Setoid/Hom.agda", "module Setoid.Hom", "module QIT.Setoid.Hom"),
        ("QIT/Setoid/Iso.agda", "module Setoid.Iso", "module QIT.Setoid.Iso"),
        # Parameterized modules - simple patterns
        (
            "QIT/Mobile/Base.agda",
            r"module Mobile\.Base\s*\(",
            "module QIT.Mobile.Base (",
        ),
        (
            "QIT/Mobile/Cocontinuity.agda",
            r"module Mobile\.Cocontinuity\s*\(",
            "module QIT.Mobile.Cocontinuity (",
        ),
        (
            "QIT/Mobile/Colimit.agda",
            r"module Mobile\.Colimit\s*\(",
            "module QIT.Mobile.Colimit (",
        ),
        (
            "QIT/Mobile/Equivalence.agda",
            r"module Mobile\.Equivalence\s*\(",
            "module QIT.Mobile.Equivalence (",
        ),
        (
            "QIT/Mobile/Functor.agda",
            r"module Mobile\.Functor\s*\(",
            "module QIT.Mobile.Functor (",
        ),
        # Complex parameterized modules
        (
            "QIT/Cocontinuity.agda",
            r"module Cocontinuity\s*\{",
            "module QIT.Cocontinuity {",
        ),
        ("QIT/Colimit.agda", r"module Colimit\s*\{", "module QIT.Colimit {"),
        (
            "QIT/ContainerFunctor.agda",
            r"module ContainerFunctor\s*\{",
            "module QIT.ContainerFunctor {",
        ),
        ("QIT/Plump.agda", r"module Plump\s*\{", "module QIT.Plump {"),
        # Special case for Setoid.Sigma - multiline
        (
            "QIT/Setoid/Sigma.agda",
            r"module Setoid\.Sigma\s*$",
            "module QIT.Setoid.Sigma",
        ),
    ]

    for file_path_str, old_pattern, new_text in module_updates:
        file_path = Path(file_path_str)
        if not file_path.exists():
            continue

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            original_content = content
            content = re.sub(
                old_pattern, new_text, content, count=1, flags=re.MULTILINE
            )

            if content != original_content:
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(content)
                print(f"  Updated module: {file_path}")

        except Exception as e:
            print(f"  Error updating module in {file_path}: {e}")

    # Step 3: Handle special namespace conflicts
    print("\nStep 3: Resolving namespace conflicts...")

    # The key issue is QIT.Cocontinuity vs QIT.Colimit both having Diagram
    # Solution: Use qualified imports in Cocontinuity to avoid conflicts
    cocont_path = Path("QIT/Cocontinuity.agda")
    if cocont_path.exists():
        try:
            with open(cocont_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Replace the problematic open with a qualified import approach
            # Change "open import QIT.Colimit" to qualified import
            content = re.sub(
                r"open import QIT\.Colimit\s*$",
                "import QIT.Colimit as C",
                content,
                flags=re.MULTILINE,
            )

            # Change "open QIT.Colimit ≤p" to "open C ≤p"
            content = re.sub(r"open QIT\.Colimit (≤p)", r"open C \1", content)

            # Update references to "Colim" to use proper qualified names
            # The Colim is inside the C ≤p opening, so it should be available as just "Colim"
            # But we need to handle the Colim.Colim references
            content = re.sub(r"Colim\.Colim", "Colim", content)

            with open(cocont_path, "w", encoding="utf-8") as f:
                f.write(content)
            print(f"  Fixed namespace conflicts: {cocont_path}")

        except Exception as e:
            print(f"  Error fixing namespace conflicts in {cocont_path}: {e}")

    # Step 4: Fix mobile module references to Colim
    print("\nStep 4: Fixing mobile module references...")

    mobile_files = ["QIT/Mobile/Cocontinuity.agda", "QIT/Mobile/Colimit.agda"]
    for mobile_file in mobile_files:
        mobile_path = Path(mobile_file)
        if mobile_path.exists():
            try:
                with open(mobile_path, "r", encoding="utf-8") as f:
                    content = f.read()

                original_content = content

                # Update "open Colim" references - these need to be "open QIT.Colimit"
                content = re.sub(r"\bopen\s+Colim\b", "open QIT.Colimit", content)

                if content != original_content:
                    with open(mobile_path, "w", encoding="utf-8") as f:
                        f.write(content)
                    print(f"  Updated mobile references: {mobile_path}")

            except Exception as e:
                print(f"  Error updating mobile file {mobile_path}: {e}")

    # Step 5: Test the build
    print("\nStep 5: Testing build...")
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

            # Try to provide helpful diagnostics
            if "AmbiguousName" in result.stderr:
                print("\n🔧 DIAGNOSTIC: Ambiguous name errors detected.")
                print("   This usually means two modules are exporting the same name.")
                print("   Consider using qualified imports or renaming.")

            elif "ModuleNameDoesntMatchFileName" in result.stderr:
                print("\n🔧 DIAGNOSTIC: Module name mismatch detected.")
                print("   Check that module declarations match their file paths.")

            elif "NotInScope" in result.stderr:
                print("\n🔧 DIAGNOSTIC: Name not in scope errors detected.")
                print("   Check import statements and module openings.")

            return False

    except FileNotFoundError:
        print("❌ ERROR: agda command not found!")
        print("   Make sure Agda is installed and in your PATH.")
        return False

    except Exception as e:
        print(f"❌ ERROR running build test: {e}")
        return False


if __name__ == "__main__":
    print("Starting complete QIT refactor...")
    success = complete_refactor()

    if success:
        print("\n🎉 Refactor completed successfully!")
        print("\nYour QIT library has been successfully moved to the QIT/ namespace.")
        print("All imports have been updated and the build is working.")
    else:
        print("\n💥 Refactor encountered issues!")
        print("\nPlease review the error messages above and fix any remaining issues.")
        print("You may need to manually resolve some namespace conflicts.")

    sys.exit(0 if success else 1)
