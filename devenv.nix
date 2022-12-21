{ pkgs, inputs, lib, ... }:
let
  fenix = inputs.fenix.packages.${pkgs.system};
  toolchain = fenix.complete;
in 
{
  packages = [ toolchain.toolchain fenix.rust-analyzer pkgs.cargo-llvm-cov pkgs.cargo-edit pkgs.cargo-flamegraph pkgs.kakoune-cr pkgs.xplr ];

  enterShell = ''
    export EDITOR=kaks
    vscode-settings
  '';

  scripts.kaks.exec = ''
    kcr open --session=leonie --client=client0 $@
  '';

  scripts.vscode-settings.exec = ''
    mkdir -p .vscode
    touch -a .vscode/settings.json

    cat <<EOF > .vscode/settings.json
    {
      "rust-analyzer.cargo.sysroot": "${toolchain.toolchain}",
      "rust-analyzer.server.path": "${fenix.rust-analyzer}/bin/rust-analyzer"
    }
    EOF
  '';

  pre-commit = {
    tools = {
      cargo = lib.mkForce toolchain.cargo;
      rustfmt = lib.mkForce toolchain.rustfmt;
      clippy = lib.mkForce toolchain.clippy;
    };
    hooks = {
      rustfmt.enable = true;

      cargo-test = {
        enable = false;
        name = "cargo-test";
        description = "run tests via cargo test";
        entry = "${toolchain.cargo}/bin/cargo test";
        types = ["rust"];
        files = "\\.rs$";
        pass_filenames = false;
      };

      cargo-clippy = {
        enable = true;
        name = "cargo-clippy";
        description = "run clippy linter";
        entry = "${toolchain.cargo}/bin/cargo clippy -- -D warnings";
        types = ["rust"];
        pass_filenames = false;
      };

      
      cargo-llvm-cov = 
        let
          wrapper = pkgs.symlinkJoin {
            name = "cargo-llvm-cov-wrapped";
            paths = [ pkgs.cargo-llvm-cov ];
            nativeBuildInputs = [ pkgs.makeWrapper ];
            postBuild = ''
              wrapProgram $out/bin/cargo-llvm-cov \
                --prefix PATH : ${lib.makeBinPath [ pkgs.cargo-llvm-cov ]}
            '';
          };
      in
      {
        enable = true;
        name = "cargo llvm-cov";
        description = "run coverage test via llvm-cov";
        entry = "${wrapper}/bin/cargo-llvm-cov llvm-cov --open";
        files = "(\\.rs$)|(^Cargo\\.toml$)|(^Cargo\\.lock$)";
        pass_filenames = false;
	      stages = [ "push" ];
      };
    };
  };
}
