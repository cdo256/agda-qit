{
  perSystem =
    { self', pkgs, ... }:
    {
      devShells.default = pkgs.mkShell {
        buildInputs = with self'.packages; [
          self'.packages.agda
          self'.packages.just-agda
        ];
      };
    };
}
