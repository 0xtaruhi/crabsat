// Runs the crabsat wasm32-unknown-unknown smoke test (see src/lib.rs).
import { readFileSync } from "node:fs";

const path = process.argv[2];
const { instance } = await WebAssembly.instantiate(readFileSync(path), {});
const result = instance.exports.smoke();
console.log(`smoke() = ${result}`);
process.exit(result === 0 ? 0 : 1);
