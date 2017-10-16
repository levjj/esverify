var webpack = require('webpack'),
    path = require('path');

var libraryName = 'esverify';

module.exports = {
  entry: [
    __dirname + '/index'
  ],
  output: {
    path: __dirname,
    filename: libraryName + '.js',
    library: libraryName,
    libraryTarget: 'umd',
    umdNamedDefine: true
  },
  externals: {
    esprima: 'commonjs esprima',
    child_process: 'commonjs child_process'
  },
  module: {
    loaders: [
      {test: /\.ts$/, loader: 'ts', exclude: /node_modules/}
    ]
  },
  resolve: {
    root: path.resolve('./src'),
    extensions: ['.js', '.ts']
  }
};
