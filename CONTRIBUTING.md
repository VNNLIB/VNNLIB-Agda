# Contributing to VNNLIB-Agda

## Setting up the project

To setup the project to begin development:

1. Clone the repository with submodules:
   ```bash
   git clone --recurse-submodules https://github.com/VNNLIB/VNNLIB-Agda.git
   cd VNNLIB-Agda
   ```
   If you have already cloned the repository without submodules, initialize them:
   ```bash
   git submodule update --init --recursive
   ```

2. Install the correct version of the Agda standard library.

## Updating the grammar

When changes are made to the [grammar](https://github.com/VNNLIB/VNNLIB-Standard/blob/main/grammar.cf) in the [VNN-LIB Standard](https://github.com/VNNLIB/VNNLIB-Standard), then the following procedure should be performed.

In order to build the grammar you must have the following tools installed:
- [BNFC](https://github.com/BNFC/bnfc) (v2.9.5)
- [Flex](https://github.com/westes/flex) (v2.6.4)
- [Bison](https://www.gnu.org/software/bison/) (3.8.2)

The versions above are known to work although others may work as well.


1. Get the required version of the grammar, by navigating into the submodule `VNNLIB-Standard` directory, pulling and then checking out the required commit.
```bash
cd VNNLIB-Standard
git pull
git checkout REF
cd ..
```
where `REF` is either a commit hash or a tag for the commit you want to update to.

2. Generate the new version of the parser for the grammar using:
```bash
bnfc -d --agda VNNLIB-Standard/grammar.cf -o src -p VNNLIB
```

## Making a release

1. Update `README.md` with a new entry to the compatibility table if applicable.

2. Update `CHANGELOG.md` with the new version and a list of changes.

3. Create a new Release on GitHub:
   - Tag the version (e.g., `v1.0.1`).
   - Provide a title and description.
   - Publish the release.