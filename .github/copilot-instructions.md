# Polychromatic Repository - Copilot Instructions

## Repository Overview

This repository contains a formalization of polychromatic colourings of integers in the Lean theorem prover. Given a finite set S of integers, a colouring is S-polychromatic if every translate of S contains an element of each colour class. The primary goal is to prove that for any set S of size 4, there exists an S-polychromatic colouring in 3 colours.

**Project Type**: Mathematical theorem proving + Website generation  
**Primary Language**: Lean 4 (formal proof)  
**Supporting Languages**: C++, Python, Ruby/Jekyll  
**Repository Size**: ~1.7GB (includes dependencies)  
**Source Code**: ~1,122 lines of Lean proofs

## Critical Build Requirements

### ⚠️ ALWAYS Run Cache Before Building

**MOST IMPORTANT**: Before building Lean code, you **MUST** run `lake exe cache get` to download pre-compiled mathlib binaries. Without this, building will take 1+ hours and may timeout.

```bash
cd Lean
lake exe cache get  # CRITICAL: Always run this first!
lake build          # Only after cache is downloaded
```

**Build Time**:
- With cache: ~2-5 minutes for incremental builds
- Without cache: 60+ minutes (mathlib has 1000+ files)

## Repository Structure

### Root Directory Files
```
.devcontainer/          # Docker container with elan/Lean setup
.github/
  ├── workflows/
  │   └── lean_action_ci.yml  # Main CI pipeline
  └── dependabot.yml    # Dependency update config
Generation/             # C++ code generation tools
Lean/                   # Main Lean 4 proof code
Verso/                  # Website generation code (Lean)
site/                   # Jekyll website source
requirements.txt        # Python dependencies (z3-solver, tqdm)
README.md              # Project documentation
```

### Lean Directory (`Lean/`)
**Location**: `/Lean`  
**Purpose**: Main Lean 4 formalization code  
**Toolchain**: `leanprover/lean4:v4.25.0-rc2`  
**Build System**: Lake (Lean's build tool)

```
Lean/
├── lakefile.toml           # Lake build configuration
├── lean-toolchain          # Specifies Lean version
├── lake-manifest.json      # Dependency lock file
├── Polychromatic.lean      # Root module (imports all)
└── Polychromatic/          # Source files
    ├── Basic.lean          # Basic definitions
    ├── Colouring.lean      # Colouring definitions
    ├── DiscreteProbability.lean
    ├── Existence.lean
    ├── ForMathlib/         # Utilities for mathlib
    │   └── Misc.lean
    ├── LocalLemma.lean
    ├── LovaszFunction.lean
    └── Main.lean           # Main theorem (currently sorry)
```

**Key Configuration** (`lakefile.toml`):
- Project name: `polychromatic`
- Dependencies: mathlib, subverso
- Linter rules enabled: line length (100 chars), multiGoal, flexible tactics

### Verso Directory (`Verso/`)
**Location**: `/Verso`  
**Purpose**: Generate website content from Lean documentation  
**Toolchain**: `leanprover/lean4:nightly-2025-07-06` (different from main Lean!)

```
Verso/
├── lakefile.toml           # Separate Lake config
├── lean-toolchain          # Different Lean version!
├── PolychromaticMain.lean  # Entry point for docs generation
├── PolychromaticSite.lean  # Site content definitions
├── PolychromaticSite/      # Site content modules
└── Berso/                  # Blog generation framework
    └── BersoBlog/
```

**Important**: Verso uses a **different Lean version** (nightly-2025-07-06) than the main project.

### Site Directory (`site/`)
**Location**: `/site`  
**Purpose**: Jekyll static site generation  
**Theme**: dinky (remote theme: pages-themes/dinky@v0.2.0)

```
site/
├── Gemfile                 # Ruby dependencies
├── _config.yml             # Jekyll configuration
├── _includes/              # HTML partials
├── _layouts/               # Page templates
├── _sass/                  # Stylesheets
├── -verso-css/             # Verso-generated CSS
└── -verso-js/              # Verso-generated JS
```

### Generation Directory (`Generation/`)
**Location**: `/Generation`  
**Purpose**: C++ code for generating explicit colourings  
**File**: `coloring-integers.cpp` - Generates periodic colourings for quadruples

## Build and Validation Workflow

### 1. Building Lean Code

```bash
cd Lean

# STEP 1: ALWAYS get cache first (critical!)
lake exe cache get

# STEP 2: Build the project
lake build

# STEP 3: Build specific module (faster)
lake build Polychromatic
```

**Common Issues**:
- If `lake exe cache get` fails with network errors, the build will take 60+ minutes
- Cache downloads from `lakecache.blob.core.windows.net`
- Without cache, expect to build 1000+ mathlib files

### 2. Generating Website Content

```bash
cd Verso

# Generate documentation pages (outputs to ../site/_pages)
lake exe docs
```

**Output**: Creates markdown/HTML pages in `site/_pages/` directory

### 3. Building Jekyll Site

```bash
cd site

# Install Ruby dependencies (first time only)
bundle install

# Build site
bundle exec jekyll build --destination ../_site --baseurl "/Polychromatic"

# Or serve locally for development
bundle exec jekyll serve
```

**Ruby Version**: 3.1 (as specified in CI workflow)

### 4. Compiling C++ Generation Tool

```bash
cd Generation

# Compile with OpenMP support for parallelism
g++ -O3 -fopenmp coloring-integers.cpp -o coloring-integers

# Run (no input required)
./coloring-integers
```

## Continuous Integration Pipeline

**File**: `.github/workflows/lean_action_ci.yml`  
**Triggers**: Push to `main`, pull requests to `main`, manual dispatch  
**Runner**: `ubuntu-latest`

### CI Build Steps (in order):

1. **Checkout code**
2. **Build Lean files** - Uses `leanprover/lean-action@main`
   - Runs `lake build` in `Lean/` directory
   - Includes `mk_all-check: true` to verify all imports
3. **Run Verso** - Generates documentation
   - `cd Verso && lake exe docs`
4. **Setup Ruby 3.1** - For Jekyll
   - Auto-runs `bundle install` with caching
5. **Build Jekyll site**
   - `cd site && bundle exec jekyll build`
6. **Upload Pages artifact** - For GitHub Pages deployment
7. **Clean annotations** (on push only)
   - Removes `-- ANCHOR:` and `-- ANCHOR_END:` lines from .lean files
   - Deletes Verso, site, _site directories
8. **Commit to release branch** (on push only)
   - Force-pushes cleaned code to `release` branch
9. **Deploy to GitHub Pages** (separate job)

**Important**: The CI uses the `lean-action` which automatically handles `lake exe cache get`, so cache is available in CI.

## Making Changes

### Modifying Lean Proofs

1. Edit `.lean` files in `Lean/Polychromatic/`
2. Check syntax: Files should type-check in your editor (VS Code with Lean extension)
3. Build to verify: `cd Lean && lake build`
4. **Do not** remove `-- ANCHOR:` comments - they're used for documentation extraction

### Modifying Website Content

1. Edit Lean documentation in `Verso/PolychromaticSite/`
2. Regenerate: `cd Verso && lake exe docs`
3. Check output in `site/_pages/`
4. Build site: `cd site && bundle exec jekyll build`

### Modifying Jekyll Theme/Layout

1. Edit files in `site/_layouts/`, `site/_includes/`, or `site/_sass/`
2. Test locally: `cd site && bundle exec jekyll serve`
3. View at `http://localhost:4000/Polychromatic/`

## Common Pitfalls and Workarounds

### 1. Long Build Times
**Problem**: `lake build` takes over an hour  
**Cause**: Forgot to run `lake exe cache get`  
**Solution**: Always run `lake exe cache get` before building

### 2. Different Lean Versions
**Problem**: Verso and main Lean code use different toolchains  
**Note**: This is intentional. Verso uses nightly-2025-07-06, main uses v4.25.0-rc2  
**Action**: Don't try to unify them; keep separate

### 3. Network Restrictions
**Problem**: `lake exe cache get` fails with "Could not resolve host"  
**Workaround**: In restricted environments, you may need to build without cache (very slow) or request access to `lakecache.blob.core.windows.net`

### 4. Jekyll Bundle Install Fails
**Problem**: `bundle install` fails in `site/` directory  
**Solution**: Ensure Ruby 3.1+ is installed. On Ubuntu: `sudo apt-get install ruby-full build-essential`

### 5. Missing `lake` Command
**Problem**: `lake: command not found`  
**Solution**: Install elan (Lean version manager):
```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
# Or on Ubuntu: sudo apt-get install elan
```

### 6. Git Ignores
**Important**: The following are git-ignored:
- `*/.lake/` - Lean build artifacts
- `.python-version` - Python version specifier
- `*/_site/` - Jekyll build output
- `*/vendor/` - Ruby vendor bundle
- `.DS_Store` - macOS metadata

## Development Tools

### Lean 4 Setup
- **Editor**: VS Code with Lean 4 extension (recommended)
- **Version Manager**: elan
- **Build Tool**: lake
- **Package Manager**: lake (uses lakefile.toml)

### Linting Rules
Configured in `Lean/lakefile.toml`:
- Unicode function arrows: `fun a ↦ b`
- No auto implicit variables
- Line length limit: 100 characters
- No multiple active goals in tactics
- No rigid tactics after flexible tactics

### Python Dependencies
File: `requirements.txt`
```
tqdm==4.67.1        # Progress bars
z3-solver==4.15.0.0 # SMT solver
```

Install: `pip install -r requirements.txt`

## Key Architectural Notes

1. **Main Theorem**: Located in `Lean/Polychromatic/Main.lean`, currently contains `sorry` (unfinished proof)
2. **Mathlib Dependency**: Heavy use of mathlib for basic mathematics
3. **Subverso**: Used for documentation generation (literate programming)
4. **Annotation System**: `-- ANCHOR:` and `-- ANCHOR_END:` mark code sections for documentation
5. **Release Branch**: The `release` branch contains cleaned code without annotations
6. **GitHub Pages**: Published from artifacts, available at `https://b-mehta.github.io/Polychromatic/`

## Quick Reference Commands

```bash
# Full build from scratch
cd Lean && lake exe cache get && lake build

# Incremental build after changes
cd Lean && lake build

# Build single module
cd Lean && lake build Polychromatic.Colouring

# Generate documentation
cd Verso && lake exe docs

# Build website
cd site && bundle exec jekyll build

# Serve website locally
cd site && bundle exec jekyll serve

# Clean Lean build
cd Lean && lake clean

# Update dependencies
cd Lean && lake update
```

## Trust These Instructions

This documentation has been tested and validated. If something doesn't work as described, verify you're running commands in the correct directory and have run prerequisites (especially `lake exe cache get`). Only search for additional information if these instructions are incomplete or produce errors you cannot resolve by following the troubleshooting steps.
