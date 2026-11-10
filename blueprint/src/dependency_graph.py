"""Render a clickable dependency graph for local file previews."""

from textwrap import fill

from plasTeX.PackageResource import PackagePreCleanupCB


def render_graph(document):
    graph = document.userdata["dep_graph"]["graphs"][document]
    dot = graph.to_dot(document.userdata["dep_graph"]["shapes"]).tred()
    dot.graph_attr.update(bgcolor="white", pad="0.2")
    dot.node_attr.update(fontname="sans-serif", fontsize="10")
    for node in graph.nodes:
        title = node.attributes["title"].textContent
        label = fill(f"{node.caption} {title}", width=30)
        dot.get_node(node.id).attr.update(label=label, URL=str(node.url))

    output = "dependency-graph.svg"
    dot.draw(output, prog="dot")
    return [output]


def ProcessOptions(options, document):
    data = document.userdata["dep_graph"]
    data.setdefault("shapes", {"definition": "box"})["assumption"] = "box"
    data["legend"].append(("Amber boxes", "external hypotheses in the Lean theorem types"))
    color = data["colorizer"]
    fillcolor = data["fillcolorizer"]
    data["colorizer"] = lambda node: "#8a5a12" if node.thmName == "assumption" else color(node)
    data["fillcolorizer"] = lambda node: "#ffe8b3" if node.thmName == "assumption" else fillcolor(node)
    document.addPackageResource(PackagePreCleanupCB(data=render_graph))
