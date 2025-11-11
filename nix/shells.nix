{
  perSystem =
    { self', pkgs, ... }:
    {
      devShells.default = pkgs.mkShell {
        buildInputs = with self'.packages; [
          agda
          #pkgs.haskellPackages.agda-language-server
          self'.packages.just-agda
        ];
      };
    };
}
