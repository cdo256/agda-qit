{ inputs, ... }:
{
  perSystem =
    { system, pkgs, ... }:
    {
      config.packages = rec {
        agda-base = pkgs.agda;
        agda = agda-base.withPackages (ps: [
          ps.standard-library
          #ps.cubical
        ]);
        agda2-mode = pkgs.emacsPackages.agda2-mode;
        just-agda = inputs.just-agda.packages.${system}.just-agda.override ({
          agda2-mode = pkgs.emacsPackages.agda2-mode;
        });
      };
    };
}
{ inputs, ... }:
{
  perSystem =
    { system, pkgs, ... }:
    {
      config.packages = rec {
        agda-base = pkgs.agda;
        agda = agda-base.withPackages (ps: [
          ps.standard-library
          ps.cubical
        ]);
        tex = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            scheme-medium
            latexmk
            standalone
            pgf
            amsmath
            biblatex
            tikz-cd
            latex-bin
            minted
            #ifxetex
            #ifluatex
            xifthen
            xcolor
            polytable
            etoolbox
            environ
            #xparse
            xkeyval
            ifmtarg
            lazylist
            newunicodechar
            catchfilebetweentags
            titling
            dirtree
            ;
        };
      };
    };
}
