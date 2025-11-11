{
  description = "MSc Project on Virtual Sets";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs = {
      type = "github";
      owner = "nixos";
      repo = "nixpkgs";
      #ref = "21.11"; # Agda 2.6.2
      ref = "25.05"; # Agda 2.7.0.1
    };
    just-agda = {
      type = "github";
      owner = "cdo256";
      repo = "just-agda";
      ref = "main";
    };
    #agda-cubical = {
    #  type = "github";
    #  owner = "agda";
    #  repo = "cubical";
    #  ref = "master";
    #};
  };

  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
      ];
      imports = [
        ./nix/args.nix
        ./nix/packages.nix
        ./nix/shells.nix
      ];
    };
}
