export interface Options {
  filename: string,
  local: boolean,
  z3path: string,
  remoteURL: string,
  logMessages: boolean,
  colorLog: boolean
};

const defaultOptions: Readonly<Options> = {
  filename: "",
  local: true,
  z3path: "z3",
  remoteURL: "/z3",
  logMessages: false,
  colorLog: true
};

export function setOptions(opts: Partial<Options>) {
  options = Object.assign({}, defaultOptions, opts);
}

export let options: Readonly<Options> = defaultOptions; // global singleton options object
