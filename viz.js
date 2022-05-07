const d3 = require("d3");
d3.selectAll("svg > *").remove();

var width = svg.width.baseVal.value;
var height = svg.height.baseVal.value;

const nodeList = Node.atoms(true);
const edgeList = Edge.atoms(true);
const colorList = Color.atoms(true);

var colorLib = ["#FF0000", "#FFFF00", "#00FF00", "#0000FF"];

var colors = [];
colorList.forEach((c, i) => {
  var color = {
    id: c.toString().slice(-1),
    nodes: c.nodeSet.toString().split("\n"),
    fill: colorLib[i],
  };
  colors.push(color);
});

var nodes = [];
nodeList.forEach((n, i) => {
  var node = {
    id: n.toString().slice(-1),
    fill: colors.find((c) => c.nodes.includes(n.toString())).fill,
  };
  nodes.push(node);
});

var edges = [];
edgeList.forEach((e, i) => {
  pair = e.nodePair.toString().split("\n");
  var edge = {
    source: pair[0].slice(-1),
    target: pair[1].slice(-1),
  };
  edges.push(edge);
});

const graph = {
  nodes: nodes,
  links: edges,
};

// Credit: https://d3-graph-gallery.com/graph/network_basic.html
function display(data) {
  // Initialize the links
  const link = d3
    .select(svg)
    .selectAll("line")
    .data(data.links)
    .join("line")
    .style("stroke", "#aaa");

  // Initialize the nodes
  const node = d3
    .select(svg)
    .selectAll("circle")
    .data(data.nodes)
    .join("circle")
    .attr("r", 20)
    .style("fill", (d, i) => {
      return d.fill;
    });

  // Let's list the force we wanna apply on the network
  const simulation = d3
    .forceSimulation(data.nodes) // Force algorithm is applied to data.nodes
    .force(
      "link",
      d3
        .forceLink() // This force provides links between nodes
        .id(function (d) {
          return d.id;
        }) // This provide  the id of a node
        .links(data.links) // and this the list of links
    )
    .force("charge", d3.forceManyBody().strength(-12000 / data.nodes.length)) // This adds repulsion between nodes. Play with the -400 for the repulsion strength
    .force("center", d3.forceCenter(width / 2, height / 2)) // This force attracts nodes to the center of the svg area
    .on("end", ticked);

  // This function is run at each iteration of the force algorithm, updating the nodes position.
  function ticked() {
    link
      .attr("x1", function (d) {
        return d.source.x;
      })
      .attr("y1", function (d) {
        return d.source.y;
      })
      .attr("x2", function (d) {
        return d.target.x;
      })
      .attr("y2", function (d) {
        return d.target.y;
      });

    node
      .attr("cx", function (d) {
        return d.x + 6;
      })
      .attr("cy", function (d) {
        return d.y - 6;
      });
  }
}

display(graph);