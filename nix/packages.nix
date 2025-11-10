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
      };
    };
}
