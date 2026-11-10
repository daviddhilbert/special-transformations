"""Link Lean Blueprint declarations to the audited source revisions."""

from pathlib import Path


PAPER = "https://github.com/daviddhilbert/special-transformations/blob/a19e25fe90e2e02034e499db62df4c7b8ef0eb19/"
QE = "https://github.com/daviddhilbert/ACVF-QE/blob/939346b0a99899e22a873479364e3cc5d142731c/"


def ProcessOptions(options, document):
    entries = Path(__file__).with_name("source-links.tsv").read_text(encoding="utf-8")
    links = {}
    for entry in entries.splitlines():
        name, repo, path = entry.split("\t")
        links[name] = {"paper": PAPER, "qe": QE}[repo] + path

    def set_source_links():
        for graph in document.userdata["dep_graph"]["graphs"].values():
            for node in graph.nodes:
                node.userdata["lean_urls"] = [
                    (name, links[name]) for name in node.userdata.get("leandecls", [])
                ]

    # Run after Lean Blueprint has prepared its default documentation links.
    document.addPostParseCallbacks(160, set_source_links)
