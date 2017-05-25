export interface Options {
  filename: string,
  z3path: string,
  remote: boolean,
  z3url: string,
  qi: boolean,
  logformat: "simple" | "colored",
  quiet: boolean,
  verbose: boolean
};

const defaultOptions: Readonly<Options> = {
  filename: "",
  z3path: "z3",
  remote: false,
  z3url: "/z3",
  qi: true,
  logformat: "colored",
  quiet: true,
  verbose: false
};

export function setOptions(opts: Partial<Options>) {
  options = Object.assign({}, defaultOptions, opts);
}

export let options: Readonly<Options> = defaultOptions; // global singleton options object
