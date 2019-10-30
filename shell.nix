with import <nixpkgs> {};

stdenv.mkDerivation {
    name = "crdts";
    buildInputs = with pkgs; [
        cargo
        git
    ];
}
