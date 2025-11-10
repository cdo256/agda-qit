{ inputs, ... }:
{
  perSystem =
    { system, pkgs, ... }:
    {
      config.packages = rec {
        agda-base = pkgs.agda;
        agda = agda-base.withPackages (ps: [
          #ps.standard-library
          #ps.cubical
        ]);
        agda2-mode = pkgs.emacsPackages.agda2-mode;
        just-agda = inputs.just-agda.packages.${system}.just-agda.override ({
          agda2-mode = pkgs.emacsPackages.agda2-mode;
        });
      };
    };
}
