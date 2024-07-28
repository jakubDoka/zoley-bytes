const algorithms = [
	countCyclesPerNode,
];

let index = 0;
for (const section of document.querySelectorAll("section")) {
	const input = section.querySelector("#sample").textContent;
	const testCases = JSON.parse(input);
	let output = "";
	for (const [name, ...edges] of testCases) {
		output += JSON.stringify(algorithms[index](name, edges), null, 4) + "\n";
	}
	section.querySelector("#output").textContent = output;
	index += 1;
}

/** @param {string} name @param {[number, number][]} edges */
function countCyclesPerNode(name, edges) {
	const nodeCount = countNodes(edges);
	const cycleCounts = new Array(nodeCount).fill(0);
	const seen = new Array(nodeCount).fill(0);
	const active = new Array(nodeCount).fill(0);
	const optimized = new Array(nodeCount);
	for (const i of optimized.keys()) {
		optimized[i] = edgesOf(edges, i);
	}

	function dfs(node = 0) {
		if (active[node]) {
			return true;
		}
		active[node] = 1;
		let cycle = false;
		for (const child of optimized[node]) {
			cycle |= dfs(child);
		}
		active[node] = 0;
		cycleCounts[node] += cycle;
		return cycle;
	}

	dfs();


	return [name, cycleCounts];
}

/** @param {[number, number][]} edges @param {number} node */
function edgesOf(edges, node) {
	const result = [];
	for (const [from, to] of edges) {
		if (from === node) result.push(to);
	}
	return result;
}

/** @param {[number, number][]} edges */
function countNodes(edges) {
	return Math.max(...edges.map(([from, to]) => Math.max(from, to))) + 1;
}
