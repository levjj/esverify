module.exports = {
  root: true,
  parser: 'babel-eslint',
  parserOptions: {
    sourceType: 'module'
  },
  extends: 'airbnb-base',
  rules: {
    'no-debugger': process.env.NODE_ENV === 'production' ? 2 : 0
  },
  settings: {
    'import/resolver': {
      'webpack': {
        'config': 'webpack.config.js'
      }
    }
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
    quotes: [2, "single"]
  }
}
