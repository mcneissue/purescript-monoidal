let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs-unstable {};
in
pkgs.mkShell {
  buildInputs = with pkgs; [
    purescript
    nodejs
    spago
    nodePackages.purescript-language-server
    nodePackages.bower
    nodePackages.pulp
  ];
}
