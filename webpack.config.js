var webpack = require('webpack'),
    path = require('path'),
    yargs = require('yargs');

var libraryName = 'lively.verify',
    plugins = [],
    outputFile;

if (yargs.argv.p) {
  plugins.push(new webpack.optimize.UglifyJsPlugin({minimize: true}));
  outputFile = libraryName + '.min.js';
} else {
  outputFile = libraryName + '.js';
}

var config = {
  entry: [
    __dirname + '/index.ts'
  ],
  devtool: 'source-map',
  output: {
    path: path.join(__dirname, '/dist'),
    filename: outputFile,
    library: libraryName,
    libraryTarget: 'umd',
    umdNamedDefine: true
  },
  module: {
    loaders: [
      {test: /\.ts$/, loader: 'ts', exclude: /node_modules/}
    ]
  },
  resolve: {
    root: path.resolve('./src'),
    extensions: ['', '.js', '.ts']
  },
  plugins: plugins
};

module.exports = config;
