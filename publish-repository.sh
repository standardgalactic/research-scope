#!/usr/bin/env bash
set -Eeuo pipefail

REPO="${1:-research-scope}"
OWNER="${GITHUB_OWNER:-standardgalactic}"
DESCRIPTION="Research essays, formal methods, audio lectures, and interactive visualizations."
VISIBILITY="${VISIBILITY:-public}"

cd "$HOME/new"

command -v git >/dev/null || {
    echo "Git is required."
    exit 1
}

command -v gh >/dev/null || {
    echo "GitHub CLI (gh) is required."
    exit 1
}

gh auth status >/dev/null || {
    echo "Authenticate with: gh auth login"
    exit 1
}

if [[ "$VISIBILITY" != public && "$VISIBILITY" != private ]]; then
    echo "VISIBILITY must be public or private."
    exit 1
fi

cat > README.md <<'EOF'
# Research Scope

An interdisciplinary research collection examining
computation, formal structures, scientific modeling,
coordination, and the limits of inference.

The repository contains research essays, Lean 4
formalizations, audio lectures, synchronized subtitles,
transcripts, and an interactive HTML presentation.

## Research papers

### Differential Calculus for Datatypes

An investigation of datatype differentiation,
one-hole contexts, polynomial functors, and
the algebraic structure of data modification.

[Read PDF](differential-calculus-datatypes.pdf) |
[LaTeX source](differential-calculus-datatypes.tex) |
[Lean 4](Deriv.lean)

### Local Transitions and Global Admissibility

An examination of learned atmospheric update operators,
local-to-global composition, and the distinction between
predictive accuracy and physically admissible behavior.

[Read PDF](local-transitions-global-admissibility.pdf) |
[LaTeX source](local-transitions-global-admissibility.tex)

### Coordination After Storage

An analysis of Git repository architecture,
concurrent agents, immutable objects, reference
coordination, and admissibility boundaries.

[Read PDF](coordination-after-storage.pdf) |
[LaTeX source](coordination-after-storage.tex)

## Audio lectures

| Lecture | Audio | Transcript | Subtitles |
|---|---|---|---|
| Taking the Derivative of Data Structures | [MP3](Taking_the_Derivative_of_Data_Structures.mp3) | [TXT](Taking_the_Derivative_of_Data_Structures.txt) | [VTT](Taking_the_Derivative_of_Data_Structures.vtt) |
| Why AI Weather Models Delete Oceans | [MP3](Why_AI_Weather_Models_Delete_Oceans.mp3) | [TXT](Why_AI_Weather_Models_Delete_Oceans.txt) | [VTT](Why_AI_Weather_Models_Delete_Oceans.vtt) |
| Why 5,000 AI Agents Break Git | [MP3](Why_5,000_AI_Agents_Break_Git.mp3) | [TXT](Why_5,000_AI_Agents_Break_Git.txt) | [VTT](Why_5,000_AI_Agents_Break_Git.vtt) |

## Interactive presentation

[Open Research Scope](research-scope.html)

The HTML presentation provides an interface to
the accompanying research audio and transcripts.

## Transcription utilities

`fix_transcription_errors.sh` supports correction
of transcription and subtitle files.

## Repository structure

The repository retains the original flat layout,
allowing existing relative paths to remain valid.

## Author

Flyxion  
Independent Researcher

## License

MIT License. See [LICENSE](LICENSE).

The license applies to the repository contents
unless otherwise indicated. Third-party material
retains its original rights.
EOF

YEAR="$(date +%Y)"

cat > LICENSE <<EOF
MIT License

Copyright (c) $YEAR Flyxion

Permission is hereby granted, free of charge, to any
person obtaining a copy of this software and associated
documentation files (the "Software"), to deal in the
Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice
shall be included in all copies or substantial portions
of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY
OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT
LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
EOF

cat > .gitignore <<'EOF'
# LaTeX intermediate files
*.aux
*.log
*.out
*.toc
*.fls
*.fdb_latexmk
*.synctex.gz
*.bbl
*.blg
*.nav
*.snm
*.vrb

# Editor temporary files
*~
*.swp
*.swo
*.bak

# Python caches
__pycache__/
*.pyc

# Local environments
.env
.env.*
!.env.example

# Local transcription correction logs
corrections.log
EOF

if [[ ! -d .git ]]; then
    git init -b main
fi

git branch -M main

# Check for GitHub repository before changing remotes.
if gh repo view "$OWNER/$REPO" >/dev/null 2>&1; then
    echo "Repository $OWNER/$REPO already exists."
    echo "Refusing to overwrite or attach automatically."
    exit 1
fi

# Stage all non-ignored files, including MP3/PDF assets.
git add -A

echo
echo "Files staged for commit:"
git diff --cached --stat
echo

# Avoid empty commits.
if ! git diff --cached --quiet; then
    git commit -m "Initial research collection"
fi

# Create remote and push.
gh repo create "$OWNER/$REPO" \
    "--$VISIBILITY" \
    --description "$DESCRIPTION" \
    --source . \
    --remote origin \
    --push

echo
echo "Repository published:"
echo "https://github.com/$OWNER/$REPO"
echo
echo "GitHub Pages can be enabled under:"
echo "https://github.com/$OWNER/$REPO/settings/pages"
