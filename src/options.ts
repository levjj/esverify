export interface Options {
  filename: string,
  remote: boolean,
  z3path: string,
  z3url: string,
  quiet: boolean,
  logformat: "simple" | "colored"
};

const defaultOptions: Readonly<Options> = {
  filename: "",
  remote: false,
  z3path: "z3",
  z3url: "/z3",
  quiet: true,
  logformat: "colored"
};

export function setOptions(opts: Partial<Options>) {
  options = Object.assign({}, defaultOptions, opts);
}

export let options: Readonly<Options> = defaultOptions; // global singleton options object
