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
{
  perSystem =
    { self', pkgs, ... }:
    {
      devShells.default = pkgs.mkShell {
        buildInputs = with self'.packages; [
          agda
          #pkgs.haskellPackages.agda-language-server
          (pkgs.python312.withPackages (p: [
            p.matplotlib
          ]))
          pkgs.texlab
          pkgs.ltex-ls
          pkgs.pandoc
          tex
          pkgs.fira-mono
          pkgs.dejavu_fonts
          pkgs.fontconfig
          pkgs.julia-mono
        ];
        shellHook = ''
          #export FONTCONFIG_FILE=$HOME/.config/fontconfig/fonts.conf
          #export FONTCONFIG_PATH=${pkgs.fontconfig.out}/etc/fonts
          fc-cache -f
        '';
      };
    };
}
