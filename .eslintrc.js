module.exports = {
  root: true,
  parser: 'babel-eslint',
  parserOptions: {
    sourceType: 'module'
  },
  extends: 'airbnb-base',
  settings: {
    'import/resolver': {
      'webpack': {
        'config': 'webpack.config.js'
      }
    },
    'spaced-comment': { markers: ['/'] },
  },
  ecmaFeatures: {
    "modules": true
  },
  env: {
    meteor: true,
    browser: true,
    node: true,
    es6: true
  },
  rules: {
    'no-debugger': process.env.NODE_ENV === 'production' ? 2 : 0,
    'quotes': [1, 'single'],
    'import/extensions': [2, 'never']
  }
}
