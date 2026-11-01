{
  description = "Render PaperFormalization/Statements.lean as a typeset, cross-linked PDF";

  # Pinned to the nixos-26.05 revision this flake was evaluated against.
  # To track the release branch instead, use "github:NixOS/nixpkgs/nixos-26.05".
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/fa1373130d5a21c040a47c5dbe1913d59ed91808";

  outputs =
    { self, nixpkgs }:
    let
      inherit (nixpkgs) lib;
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = f: lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});

      deps = pkgs: rec {
        # TeX Live 2025: scheme-small plus the packages the stylesheet needs beyond it.
        # helvetic: \mathsf in the paper's excerpts uses the URW Helvetica clone (txfonts maps it to phv).
        tex = pkgs.texliveSmall.withPackages (
          ps: with ps; [
            enumitem
            environ
            fvextra
            helvetic
            lastpage
            needspace
            newunicodechar
            pdfcol
            tcolorbox
            tikzfill
            trimspaces
            txfonts
          ]
        );
        python = pkgs.python3.withPackages (ps: [ ps.fonttools ]);
        # The renderer loads every font by file path, so it only needs these directories.
        fontDirs = {
          FREEFONT_DIR = "${pkgs.freefont_ttf}/share/fonts/truetype/";
          DEJAVU_DIR = "${pkgs.dejavu_fonts}/share/fonts/truetype/";
          # nixpkgs' `inter` installs only the variable font; the static OTFs are in its release zip.
          INTER_DIR = "${pkgs.inter.src}/extras/otf/";
        };
        # Keeps XeTeX's fontconfig initialisation quiet and self-contained.
        fontsConf = pkgs.makeFontsConf {
          fontDirectories = [
            pkgs.freefont_ttf
            pkgs.dejavu_fonts
          ];
        };
        runtime = [
          tex
          python
          pkgs.poppler-utils
          pkgs.coreutils
          pkgs.gnugrep
          pkgs.gawk
        ];
        env = fontDirs // {
          FONTCONFIG_FILE = "${fontsConf}";
        };
      };
    in
    {
      packages = forAllSystems (
        pkgs:
        let
          d = deps pkgs;
          setEnv = lib.concatStringsSep " " (
            lib.mapAttrsToList (k: v: "--set ${k} ${lib.escapeShellArg v}") d.env
          );
        in
        rec {
          render-statements = pkgs.stdenvNoCC.mkDerivation {
            pname = "render-statements";
            version = "1.0";
            src = lib.fileset.toSource {
              root = ./.;
              fileset = lib.fileset.unions [
                ./build.py
                ./preamble.tex
                ./make.sh
                ./check.py
                ./citations.py
              ];
            };
            nativeBuildInputs = [ pkgs.makeWrapper ];
            dontBuild = true;
            installPhase = ''
              runHook preInstall
              share=$out/share/render-statements
              install -Dm644 -t $share build.py preamble.tex check.py citations.py
              install -Dm755 -t $share make.sh
              makeWrapper $share/make.sh $out/bin/render-statements \
                --prefix PATH : ${lib.makeBinPath d.runtime} \
                --set RENDER_TOOL_DIR $share \
                ${setEnv}
              makeWrapper ${d.python}/bin/python3 $out/bin/render-statements-check \
                --prefix PATH : ${lib.makeBinPath [ pkgs.poppler-utils ]} \
                --add-flags "-I $share/check.py"
              makeWrapper ${d.python}/bin/python3 $out/bin/render-statements-citations \
                --add-flags "-I $share/citations.py"
              runHook postInstall
            '';
            meta = {
              description = "Typeset PaperFormalization/Statements.lean (prose, verbatim Lean, typeset paper excerpts) as a PDF";
              mainProgram = "render-statements";
              platforms = lib.platforms.unix;
            };
          };
          default = render-statements;
        }
      );

      apps = forAllSystems (
        pkgs:
        let
          p = self.packages.${pkgs.stdenv.hostPlatform.system}.render-statements;
        in
        {
          default = {
            type = "app";
            program = "${p}/bin/render-statements";
            meta.description = "Build formalization.pdf: render-statements <PaperFormalization dir> [build dir]";
          };
          check = {
            type = "app";
            program = "${p}/bin/render-statements-check";
            meta.description = "Check a rendered PDF against its source: check <Statements.lean> <formalization.pdf>";
          };
          citations = {
            type = "app";
            program = "${p}/bin/render-statements-citations";
            meta.description = "Verify (or --fix) the Core.lean/Compatibility.lean line citations in Statements.lean";
          };
        }
      );

      devShells = forAllSystems (
        pkgs:
        let
          d = deps pkgs;
        in
        {
          default = pkgs.mkShell {
            packages = d.runtime;
            inherit (d) env;
          };
        }
      );

      formatter = forAllSystems (pkgs: pkgs.nixfmt);
    };
}
