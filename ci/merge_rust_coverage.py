# This file is dual licensed under the terms of the Apache License, Version
# 2.0, and the BSD License. See the LICENSE file in the root of this repository
# for complete details.

# Taken from pyca/cryptography (.github/bin/merge_rust_coverage.py).
#
# Usage: python ci/merge_rust_coverage.py <dir of .lcov files>
#
# Merges the lcov files written by ci/export_rust_coverage.py on every CI
# platform that ran its tests, and fails if any line they built is not
# covered: first each architecture's files alone (`<arch>-<uuid>.lcov`), each
# of which must cover every line its architecture builds, so that a run that
# tests only some architectures checks their coverage; then all of them
# together, reporting the combined line coverage (and writing an HTML report
# to htmlcov/ if it is under 100%). Lines between `// NO-COVERAGE-START` and
# `// NO-COVERAGE-END` are excluded.

import collections
import collections.abc
import pathlib
import sys

CoverageData = collections.abc.Mapping[str, collections.abc.Mapping[int, int]]


def plugin(coverage, coverage_data: CoverageData):
    """A plugin of the `coverage` module that reports `coverage_data`."""

    class RustCoverageFileReporter(coverage.FileReporter):
        def __init__(
            self, filename: str, coverage_data: collections.abc.Mapping[int, int]
        ) -> None:
            super().__init__(filename)
            self._data = coverage_data

        def lines(self) -> set[int]:
            return set(self._data)

        def arcs(self) -> set[tuple[int, int]]:
            return {(-1, line) for line in self._data}

    class RustCoveragePlugin(coverage.CoveragePlugin):
        def file_reporter(self, filename: str) -> coverage.FileReporter:
            return RustCoverageFileReporter(filename, coverage_data[filename])

    return RustCoveragePlugin()


def get_excluded_lines(filename: str) -> list[int]:
    """
    Parse source file for NO-COVERAGE-START/END pairs and return excluded
    lines.
    """
    excluded = []
    with open(filename) as f:
        in_excluded_block = False
        for line_num, line in enumerate(f, start=1):
            stripped = line.strip()
            if stripped == "// NO-COVERAGE-START":
                in_excluded_block = True
            elif stripped == "// NO-COVERAGE-END":
                in_excluded_block = False
            elif in_excluded_block:
                excluded.append(line_num)
    return excluded


def arch_of(lcov: pathlib.Path) -> str:
    """The architecture whose tests wrote `lcov`, `<arch>-<uuid>.lcov`."""
    return lcov.name.split("-", 1)[0]


def parse_lcovs(
    path: pathlib.Path,
    arch: str | None = None,
) -> tuple[
    CoverageData,
    dict[str, set[tuple[int, int]]],
]:
    """The lines of every lcov file in `path` (or only `arch`'s), with their
    counts summed, and the covered ones."""
    # {filename: {line_number: count}}
    raw_data = collections.defaultdict(lambda: collections.defaultdict(int))
    current_file = None
    for p in sorted(path.glob("*.lcov")):
        if arch is not None and arch_of(p) != arch:
            continue
        with p.open() as f:
            for line in f:
                line = line.strip()
                if line == "end_of_record":
                    assert current_file is not None
                    current_file = None
                    continue

                prefix, suffix = line.split(":", 1)
                match prefix:
                    case "SF":
                        current_file = raw_data[suffix]
                    case "DA":
                        assert current_file is not None
                        line_number, count = suffix.split(",")
                        current_file[int(line_number)] += int(count)
                    case (
                        "BRF"
                        | "BRH"
                        | "FN"
                        | "FNDA"
                        | "FNF"
                        | "FNH"
                        | "LF"
                        | "LH"
                    ):
                        # These are various forms of metadata and summary stats
                        # that we don't need.
                        pass
                    case _:
                        raise NotImplementedError(prefix)

    # Filter out lines within NO-COVERAGE blocks
    for file_name in raw_data:
        excluded_lines = get_excluded_lines(file_name)
        for line_num in excluded_lines:
            raw_data[file_name].pop(line_num, None)

    covered_lines = {
        file_name: {(-1, line) for line, c in lines.items() if c > 0}
        for file_name, lines in raw_data.items()
    }

    return raw_data, covered_lines


def uncovered(raw_data: CoverageData) -> list[tuple[str, int]]:
    """The lines of `raw_data` that no test ran."""
    return [
        (file_name, line)
        for file_name, lines in sorted(raw_data.items())
        for line, count in sorted(lines.items())
        if count == 0
    ]


def check_arches(path: pathlib.Path) -> bool:
    """Whether each architecture's lcov files in `path` alone cover every
    line they have, printing those they do not."""
    ok = True
    for arch in sorted({arch_of(p) for p in path.glob("*.lcov")}):
        raw_data, _ = parse_lcovs(path, arch)
        missing = uncovered(raw_data)
        total = sum(len(lines) for lines in raw_data.values())
        print(f"{arch}: {total - len(missing)} of {total} lines covered")
        for file_name, line in missing:
            print(f"  {file_name}:{line}")
        ok = ok and not missing
    if not ok:
        print("+++ An architecture's tests leave lines it builds uncovered +++")
    return ok


def main(coverage_loc: str):
    import coverage

    path = pathlib.Path(coverage_loc)
    print("Checking each architecture")
    arches_ok = check_arches(path)

    coverage_data = coverage.CoverageData(suffix="rust")

    print("Parsing LCOVs")
    raw_data, covered_lines = parse_lcovs(path)

    coverage_data.add_arcs(covered_lines)
    coverage_data.add_file_tracers(
        dict.fromkeys(covered_lines, "None.RustCoveragePlugin")
    )
    coverage_data.write()

    cov = coverage.Coverage(
        plugins=[lambda reg: reg.add_file_tracer(plugin(coverage, raw_data))],
    )
    print("Combining Coverage")
    cov.combine(
        data_paths=[str(path), coverage_data.data_filename()], keep=True
    )
    print("Coverage Report")
    coverage_percent = cov.report(show_missing=True)
    if coverage_percent < 100:
        print("+++ Combined coverage under 100% +++")
        cov.html_report()
        sys.exit(1)
    if not arches_ok:
        sys.exit(1)


if __name__ == "__main__":
    main(*sys.argv[1:])
