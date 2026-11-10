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
    data.setdefault("shapes", {"definition": "box"}).update(
        assumption="box", checkedimport="box"
    )
    data["legend"].extend([
        ("Amber boxes", "external hypotheses in the Lean theorem types"),
        ("Purple boxes", "checked Lean imports"),
    ])
    color = data["colorizer"]
    fillcolor = data["fillcolorizer"]
    borders = {"assumption": "#8a5a12", "checkedimport": "#4e3b9e"}
    fills = {"assumption": "#ffe8b3", "checkedimport": "#e4e0ff"}
    data["colorizer"] = lambda node: borders.get(node.thmName) or color(node)
    data["fillcolorizer"] = lambda node: fills.get(node.thmName) or fillcolor(node)
    document.addPackageResource(PackagePreCleanupCB(data=render_graph))
