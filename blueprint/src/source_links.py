"""Link Lean Blueprint declarations to the audited source revisions."""

from pathlib import Path


PAPER = "https://github.com/daviddhilbert/special-transformations/blob/932a5075ad91a825d4b8c1bf1396b2063e44fe40/"
QE = "https://github.com/daviddhilbert/ACVF-QE/blob/173708265d7959e031bf9552ee884501fc21f2cb/"
HILBERT = "https://github.com/daviddhilbert/hilbert-mathlib/blob/88bb3386f616779bfd87eb453d8a7c899ad63961/"


def ProcessOptions(options, document):
    entries = Path(__file__).with_name("source-links.tsv").read_text(encoding="utf-8")
    links = {}
    for entry in entries.splitlines():
        name, repo, path = entry.split("\t")
        links[name] = {"paper": PAPER, "qe": QE, "hilbert": HILBERT}[repo] + path

    def set_source_links():
        for graph in document.userdata["dep_graph"]["graphs"].values():
            for node in graph.nodes:
                node.userdata["lean_urls"] = [
                    (name, links[name]) for name in node.userdata.get("leandecls", [])
                ]

    # Run after Lean Blueprint has prepared its default documentation links.
    document.addPostParseCallbacks(160, set_source_links)
