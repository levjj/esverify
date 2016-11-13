// <<<<<<<<<<<<< BEGIN OF AUTO GENERATED CODE <<<<<<<<<<<<<
// Generated on 16-07-17 17:25 PDT
function Visitor() {}
Visitor.prototype.accept = function accept(node, state, path) {
  if (!node) throw new Error("Undefined AST node in Visitor.accept:\n  " + path.join(".") + "\n  " + node);
  if (!node.type) throw new Error("Strangee AST node without type in Visitor.accept:\n  " + path.join(".") + "\n  " + JSON.stringify(node));
  switch(node.type) {
    case "Node": return this.visitNode(node, state, path);
    case "SourceLocation": return this.visitSourceLocation(node, state, path);
    case "Position": return this.visitPosition(node, state, path);
    case "Program": return this.visitProgram(node, state, path);
    case "Function": return this.visitFunction(node, state, path);
    case "Statement": return this.visitStatement(node, state, path);
    case "SwitchCase": return this.visitSwitchCase(node, state, path);
    case "CatchClause": return this.visitCatchClause(node, state, path);
    case "VariableDeclarator": return this.visitVariableDeclarator(node, state, path);
    case "Expression": return this.visitExpression(node, state, path);
    case "Property": return this.visitProperty(node, state, path);
    case "Pattern": return this.visitPattern(node, state, path);
    case "Super": return this.visitSuper(node, state, path);
    case "SpreadElement": return this.visitSpreadElement(node, state, path);
    case "TemplateElement": return this.visitTemplateElement(node, state, path);
    case "Class": return this.visitClass(node, state, path);
    case "ClassBody": return this.visitClassBody(node, state, path);
    case "MethodDefinition": return this.visitMethodDefinition(node, state, path);
    case "ModuleDeclaration": return this.visitModuleDeclaration(node, state, path);
    case "ModuleSpecifier": return this.visitModuleSpecifier(node, state, path);
    case "RestProperty": return this.visitRestProperty(node, state, path);
    case "SpreadProperty": return this.visitSpreadProperty(node, state, path);
    case "Identifier": return this.visitIdentifier(node, state, path);
    case "Literal": return this.visitLiteral(node, state, path);
    case "ExpressionStatement": return this.visitExpressionStatement(node, state, path);
    case "BlockStatement": return this.visitBlockStatement(node, state, path);
    case "EmptyStatement": return this.visitEmptyStatement(node, state, path);
    case "DebuggerStatement": return this.visitDebuggerStatement(node, state, path);
    case "WithStatement": return this.visitWithStatement(node, state, path);
    case "ReturnStatement": return this.visitReturnStatement(node, state, path);
    case "LabeledStatement": return this.visitLabeledStatement(node, state, path);
    case "BreakStatement": return this.visitBreakStatement(node, state, path);
    case "ContinueStatement": return this.visitContinueStatement(node, state, path);
    case "IfStatement": return this.visitIfStatement(node, state, path);
    case "SwitchStatement": return this.visitSwitchStatement(node, state, path);
    case "ThrowStatement": return this.visitThrowStatement(node, state, path);
    case "TryStatement": return this.visitTryStatement(node, state, path);
    case "WhileStatement": return this.visitWhileStatement(node, state, path);
    case "DoWhileStatement": return this.visitDoWhileStatement(node, state, path);
    case "ForStatement": return this.visitForStatement(node, state, path);
    case "ForInStatement": return this.visitForInStatement(node, state, path);
    case "Declaration": return this.visitDeclaration(node, state, path);
    case "ThisExpression": return this.visitThisExpression(node, state, path);
    case "ArrayExpression": return this.visitArrayExpression(node, state, path);
    case "ObjectExpression": return this.visitObjectExpression(node, state, path);
    case "FunctionExpression": return this.visitFunctionExpression(node, state, path);
    case "UnaryExpression": return this.visitUnaryExpression(node, state, path);
    case "UpdateExpression": return this.visitUpdateExpression(node, state, path);
    case "BinaryExpression": return this.visitBinaryExpression(node, state, path);
    case "AssignmentExpression": return this.visitAssignmentExpression(node, state, path);
    case "LogicalExpression": return this.visitLogicalExpression(node, state, path);
    case "MemberExpression": return this.visitMemberExpression(node, state, path);
    case "ConditionalExpression": return this.visitConditionalExpression(node, state, path);
    case "CallExpression": return this.visitCallExpression(node, state, path);
    case "SequenceExpression": return this.visitSequenceExpression(node, state, path);
    case "ArrowFunctionExpression": return this.visitArrowFunctionExpression(node, state, path);
    case "YieldExpression": return this.visitYieldExpression(node, state, path);
    case "TemplateLiteral": return this.visitTemplateLiteral(node, state, path);
    case "TaggedTemplateExpression": return this.visitTaggedTemplateExpression(node, state, path);
    case "AssignmentProperty": return this.visitAssignmentProperty(node, state, path);
    case "ObjectPattern": return this.visitObjectPattern(node, state, path);
    case "ArrayPattern": return this.visitArrayPattern(node, state, path);
    case "RestElement": return this.visitRestElement(node, state, path);
    case "AssignmentPattern": return this.visitAssignmentPattern(node, state, path);
    case "ClassExpression": return this.visitClassExpression(node, state, path);
    case "MetaProperty": return this.visitMetaProperty(node, state, path);
    case "ImportDeclaration": return this.visitImportDeclaration(node, state, path);
    case "ImportSpecifier": return this.visitImportSpecifier(node, state, path);
    case "ImportDefaultSpecifier": return this.visitImportDefaultSpecifier(node, state, path);
    case "ImportNamespaceSpecifier": return this.visitImportNamespaceSpecifier(node, state, path);
    case "ExportNamedDeclaration": return this.visitExportNamedDeclaration(node, state, path);
    case "ExportSpecifier": return this.visitExportSpecifier(node, state, path);
    case "ExportDefaultDeclaration": return this.visitExportDefaultDeclaration(node, state, path);
    case "ExportAllDeclaration": return this.visitExportAllDeclaration(node, state, path);
    case "AwaitExpression": return this.visitAwaitExpression(node, state, path);
    case "RegExpLiteral": return this.visitRegExpLiteral(node, state, path);
    case "FunctionDeclaration": return this.visitFunctionDeclaration(node, state, path);
    case "VariableDeclaration": return this.visitVariableDeclaration(node, state, path);
    case "NewExpression": return this.visitNewExpression(node, state, path);
    case "ForOfStatement": return this.visitForOfStatement(node, state, path);
    case "ClassDeclaration": return this.visitClassDeclaration(node, state, path);
  }
  throw new Error("No visit function in AST visitor Visitor for:\n  " + path.join(".") + "\n  " + JSON.stringify(node));
}
Visitor.prototype.visitNode = function visitNode(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitSourceLocation = function visitSourceLocation(node, state, path) {
  var visitor = this;
  // start is of types Position
  node["start"] = visitor.accept(node["start"], state, path.concat(["start"]));
  // end is of types Position
  node["end"] = visitor.accept(node["end"], state, path.concat(["end"]));
  return node;
}
Visitor.prototype.visitPosition = function visitPosition(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitProgram = function visitProgram(node, state, path) {
  var visitor = this;
  // body is a list with types Statement, ModuleDeclaration
  var newElements = [];
  for (var i = 0; i < node["body"].length; i++) {
    var ea = node["body"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["body", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["body"] = newElements;
  return node;
}
Visitor.prototype.visitFunction = function visitFunction(node, state, path) {
  var visitor = this;
  // id is of types Identifier
  if (node["id"]) {
    node["id"] = visitor.accept(node["id"], state, path.concat(["id"]));
  }
  // params is a list with types Pattern
  var newElements = [];
  for (var i = 0; i < node["params"].length; i++) {
    var ea = node["params"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["params", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["params"] = newElements;
  // body is of types BlockStatement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitStatement = function visitStatement(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitSwitchCase = function visitSwitchCase(node, state, path) {
  var visitor = this;
  // test is of types Expression
  if (node["test"]) {
    node["test"] = visitor.accept(node["test"], state, path.concat(["test"]));
  }
  // consequent is a list with types Statement
  var newElements = [];
  for (var i = 0; i < node["consequent"].length; i++) {
    var ea = node["consequent"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["consequent", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["consequent"] = newElements;
  return node;
}
Visitor.prototype.visitCatchClause = function visitCatchClause(node, state, path) {
  var visitor = this;
  // param is of types Pattern
  node["param"] = visitor.accept(node["param"], state, path.concat(["param"]));
  // body is of types BlockStatement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitVariableDeclarator = function visitVariableDeclarator(node, state, path) {
  var visitor = this;
  // id is of types Pattern
  node["id"] = visitor.accept(node["id"], state, path.concat(["id"]));
  // init is of types Expression
  if (node["init"]) {
    node["init"] = visitor.accept(node["init"], state, path.concat(["init"]));
  }
  return node;
}
Visitor.prototype.visitExpression = function visitExpression(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitProperty = function visitProperty(node, state, path) {
  var visitor = this;
  // key is of types Expression
  node["key"] = visitor.accept(node["key"], state, path.concat(["key"]));
  // value is of types Expression
  node["value"] = visitor.accept(node["value"], state, path.concat(["value"]));
  return node;
}
Visitor.prototype.visitPattern = function visitPattern(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitSuper = function visitSuper(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitSpreadElement = function visitSpreadElement(node, state, path) {
  var visitor = this;
  // argument is of types Expression
  node["argument"] = visitor.accept(node["argument"], state, path.concat(["argument"]));
  return node;
}
Visitor.prototype.visitTemplateElement = function visitTemplateElement(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitClass = function visitClass(node, state, path) {
  var visitor = this;
  // id is of types Identifier
  if (node["id"]) {
    node["id"] = visitor.accept(node["id"], state, path.concat(["id"]));
  }
  // superClass is of types Expression
  if (node["superClass"]) {
    node["superClass"] = visitor.accept(node["superClass"], state, path.concat(["superClass"]));
  }
  // body is of types ClassBody
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitClassBody = function visitClassBody(node, state, path) {
  var visitor = this;
  // body is a list with types MethodDefinition
  var newElements = [];
  for (var i = 0; i < node["body"].length; i++) {
    var ea = node["body"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["body", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["body"] = newElements;
  return node;
}
Visitor.prototype.visitMethodDefinition = function visitMethodDefinition(node, state, path) {
  var visitor = this;
  // key is of types Expression
  node["key"] = visitor.accept(node["key"], state, path.concat(["key"]));
  // value is of types FunctionExpression
  node["value"] = visitor.accept(node["value"], state, path.concat(["value"]));
  return node;
}
Visitor.prototype.visitModuleDeclaration = function visitModuleDeclaration(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitModuleSpecifier = function visitModuleSpecifier(node, state, path) {
  var visitor = this;
  // local is of types Identifier
  node["local"] = visitor.accept(node["local"], state, path.concat(["local"]));
  return node;
}
Visitor.prototype.visitRestProperty = function visitRestProperty(node, state, path) {
  var visitor = this;
  // argument is of types Expression
  node["argument"] = visitor.accept(node["argument"], state, path.concat(["argument"]));
  return node;
}
Visitor.prototype.visitSpreadProperty = function visitSpreadProperty(node, state, path) {
  var visitor = this;
  // argument is of types Expression
  node["argument"] = visitor.accept(node["argument"], state, path.concat(["argument"]));
  return node;
}
Visitor.prototype.visitIdentifier = function visitIdentifier(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitLiteral = function visitLiteral(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitExpressionStatement = function visitExpressionStatement(node, state, path) {
  var visitor = this;
  // expression is of types Expression
  node["expression"] = visitor.accept(node["expression"], state, path.concat(["expression"]));
  return node;
}
Visitor.prototype.visitBlockStatement = function visitBlockStatement(node, state, path) {
  var visitor = this;
  // body is a list with types Statement
  var newElements = [];
  for (var i = 0; i < node["body"].length; i++) {
    var ea = node["body"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["body", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["body"] = newElements;
  return node;
}
Visitor.prototype.visitEmptyStatement = function visitEmptyStatement(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitDebuggerStatement = function visitDebuggerStatement(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitWithStatement = function visitWithStatement(node, state, path) {
  var visitor = this;
  // object is of types Expression
  node["object"] = visitor.accept(node["object"], state, path.concat(["object"]));
  // body is of types Statement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitReturnStatement = function visitReturnStatement(node, state, path) {
  var visitor = this;
  // argument is of types Expression
  if (node["argument"]) {
    node["argument"] = visitor.accept(node["argument"], state, path.concat(["argument"]));
  }
  return node;
}
Visitor.prototype.visitLabeledStatement = function visitLabeledStatement(node, state, path) {
  var visitor = this;
  // label is of types Identifier
  node["label"] = visitor.accept(node["label"], state, path.concat(["label"]));
  // body is of types Statement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitBreakStatement = function visitBreakStatement(node, state, path) {
  var visitor = this;
  // label is of types Identifier
  if (node["label"]) {
    node["label"] = visitor.accept(node["label"], state, path.concat(["label"]));
  }
  return node;
}
Visitor.prototype.visitContinueStatement = function visitContinueStatement(node, state, path) {
  var visitor = this;
  // label is of types Identifier
  if (node["label"]) {
    node["label"] = visitor.accept(node["label"], state, path.concat(["label"]));
  }
  return node;
}
Visitor.prototype.visitIfStatement = function visitIfStatement(node, state, path) {
  var visitor = this;
  // test is of types Expression
  node["test"] = visitor.accept(node["test"], state, path.concat(["test"]));
  // consequent is of types Statement
  node["consequent"] = visitor.accept(node["consequent"], state, path.concat(["consequent"]));
  // alternate is of types Statement
  if (node["alternate"]) {
    node["alternate"] = visitor.accept(node["alternate"], state, path.concat(["alternate"]));
  }
  return node;
}
Visitor.prototype.visitSwitchStatement = function visitSwitchStatement(node, state, path) {
  var visitor = this;
  // discriminant is of types Expression
  node["discriminant"] = visitor.accept(node["discriminant"], state, path.concat(["discriminant"]));
  // cases is a list with types SwitchCase
  var newElements = [];
  for (var i = 0; i < node["cases"].length; i++) {
    var ea = node["cases"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["cases", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["cases"] = newElements;
  return node;
}
Visitor.prototype.visitThrowStatement = function visitThrowStatement(node, state, path) {
  var visitor = this;
  // argument is of types Expression
  node["argument"] = visitor.accept(node["argument"], state, path.concat(["argument"]));
  return node;
}
Visitor.prototype.visitTryStatement = function visitTryStatement(node, state, path) {
  var visitor = this;
  // block is of types BlockStatement
  node["block"] = visitor.accept(node["block"], state, path.concat(["block"]));
  // handler is of types CatchClause
  if (node["handler"]) {
    node["handler"] = visitor.accept(node["handler"], state, path.concat(["handler"]));
  }
  // finalizer is of types BlockStatement
  if (node["finalizer"]) {
    node["finalizer"] = visitor.accept(node["finalizer"], state, path.concat(["finalizer"]));
  }
  return node;
}
Visitor.prototype.visitWhileStatement = function visitWhileStatement(node, state, path) {
  var visitor = this;
  // test is of types Expression
  node["test"] = visitor.accept(node["test"], state, path.concat(["test"]));
  // body is of types Statement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitDoWhileStatement = function visitDoWhileStatement(node, state, path) {
  var visitor = this;
  // body is of types Statement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  // test is of types Expression
  node["test"] = visitor.accept(node["test"], state, path.concat(["test"]));
  return node;
}
Visitor.prototype.visitForStatement = function visitForStatement(node, state, path) {
  var visitor = this;
  // init is of types VariableDeclaration, Expression
  if (node["init"]) {
    node["init"] = visitor.accept(node["init"], state, path.concat(["init"]));
  }
  // test is of types Expression
  if (node["test"]) {
    node["test"] = visitor.accept(node["test"], state, path.concat(["test"]));
  }
  // update is of types Expression
  if (node["update"]) {
    node["update"] = visitor.accept(node["update"], state, path.concat(["update"]));
  }
  // body is of types Statement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitForInStatement = function visitForInStatement(node, state, path) {
  var visitor = this;
  // left is of types VariableDeclaration, Pattern
  node["left"] = visitor.accept(node["left"], state, path.concat(["left"]));
  // right is of types Expression
  node["right"] = visitor.accept(node["right"], state, path.concat(["right"]));
  // body is of types Statement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitDeclaration = function visitDeclaration(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitThisExpression = function visitThisExpression(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitArrayExpression = function visitArrayExpression(node, state, path) {
  var visitor = this;
  // elements is a list with types Expression, SpreadElement
  if (node["elements"]) {
    var newElements = [];
    for (var i = 0; i < node["elements"].length; i++) {
      var ea = node["elements"][i];
      var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["elements", i])) : ea;
      if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
      else newElements.push(acceptedNodes);
    }
    node["elements"] = newElements;
  }
  return node;
}
Visitor.prototype.visitObjectExpression = function visitObjectExpression(node, state, path) {
  var visitor = this;
  // properties is a list with types Property, SpreadProperty
  var newElements = [];
  for (var i = 0; i < node["properties"].length; i++) {
    var ea = node["properties"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["properties", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["properties"] = newElements;
  return node;
}
Visitor.prototype.visitFunctionExpression = function visitFunctionExpression(node, state, path) {
  var visitor = this;
  // id is of types Identifier
  if (node["id"]) {
    node["id"] = visitor.accept(node["id"], state, path.concat(["id"]));
  }
  // params is a list with types Pattern
  var newElements = [];
  for (var i = 0; i < node["params"].length; i++) {
    var ea = node["params"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["params", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["params"] = newElements;
  // body is of types BlockStatement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitUnaryExpression = function visitUnaryExpression(node, state, path) {
  var visitor = this;
  // argument is of types Expression
  node["argument"] = visitor.accept(node["argument"], state, path.concat(["argument"]));
  return node;
}
Visitor.prototype.visitUpdateExpression = function visitUpdateExpression(node, state, path) {
  var visitor = this;
  // argument is of types Expression
  node["argument"] = visitor.accept(node["argument"], state, path.concat(["argument"]));
  return node;
}
Visitor.prototype.visitBinaryExpression = function visitBinaryExpression(node, state, path) {
  var visitor = this;
  // left is of types Expression
  node["left"] = visitor.accept(node["left"], state, path.concat(["left"]));
  // right is of types Expression
  node["right"] = visitor.accept(node["right"], state, path.concat(["right"]));
  return node;
}
Visitor.prototype.visitAssignmentExpression = function visitAssignmentExpression(node, state, path) {
  var visitor = this;
  // left is of types Pattern
  node["left"] = visitor.accept(node["left"], state, path.concat(["left"]));
  // right is of types Expression
  node["right"] = visitor.accept(node["right"], state, path.concat(["right"]));
  return node;
}
Visitor.prototype.visitLogicalExpression = function visitLogicalExpression(node, state, path) {
  var visitor = this;
  // left is of types Expression
  node["left"] = visitor.accept(node["left"], state, path.concat(["left"]));
  // right is of types Expression
  node["right"] = visitor.accept(node["right"], state, path.concat(["right"]));
  return node;
}
Visitor.prototype.visitMemberExpression = function visitMemberExpression(node, state, path) {
  var visitor = this;
  // object is of types Expression, Super
  node["object"] = visitor.accept(node["object"], state, path.concat(["object"]));
  // property is of types Expression
  node["property"] = visitor.accept(node["property"], state, path.concat(["property"]));
  return node;
}
Visitor.prototype.visitConditionalExpression = function visitConditionalExpression(node, state, path) {
  var visitor = this;
  // test is of types Expression
  node["test"] = visitor.accept(node["test"], state, path.concat(["test"]));
  // alternate is of types Expression
  node["alternate"] = visitor.accept(node["alternate"], state, path.concat(["alternate"]));
  // consequent is of types Expression
  node["consequent"] = visitor.accept(node["consequent"], state, path.concat(["consequent"]));
  return node;
}
Visitor.prototype.visitCallExpression = function visitCallExpression(node, state, path) {
  var visitor = this;
  // callee is of types Expression, Super
  node["callee"] = visitor.accept(node["callee"], state, path.concat(["callee"]));
  // arguments is a list with types Expression, SpreadElement
  var newElements = [];
  for (var i = 0; i < node["arguments"].length; i++) {
    var ea = node["arguments"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["arguments", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["arguments"] = newElements;
  return node;
}
Visitor.prototype.visitSequenceExpression = function visitSequenceExpression(node, state, path) {
  var visitor = this;
  // expressions is a list with types Expression
  var newElements = [];
  for (var i = 0; i < node["expressions"].length; i++) {
    var ea = node["expressions"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["expressions", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["expressions"] = newElements;
  return node;
}
Visitor.prototype.visitArrowFunctionExpression = function visitArrowFunctionExpression(node, state, path) {
  var visitor = this;
  // body is of types BlockStatement, Expression
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  // id is of types Identifier
  if (node["id"]) {
    node["id"] = visitor.accept(node["id"], state, path.concat(["id"]));
  }
  // params is a list with types Pattern
  var newElements = [];
  for (var i = 0; i < node["params"].length; i++) {
    var ea = node["params"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["params", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["params"] = newElements;
  return node;
}
Visitor.prototype.visitYieldExpression = function visitYieldExpression(node, state, path) {
  var visitor = this;
  // argument is of types Expression
  if (node["argument"]) {
    node["argument"] = visitor.accept(node["argument"], state, path.concat(["argument"]));
  }
  return node;
}
Visitor.prototype.visitTemplateLiteral = function visitTemplateLiteral(node, state, path) {
  var visitor = this;
  // quasis is a list with types TemplateElement
  var newElements = [];
  for (var i = 0; i < node["quasis"].length; i++) {
    var ea = node["quasis"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["quasis", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["quasis"] = newElements;
  // expressions is a list with types Expression
  var newElements = [];
  for (var i = 0; i < node["expressions"].length; i++) {
    var ea = node["expressions"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["expressions", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["expressions"] = newElements;
  return node;
}
Visitor.prototype.visitTaggedTemplateExpression = function visitTaggedTemplateExpression(node, state, path) {
  var visitor = this;
  // tag is of types Expression
  node["tag"] = visitor.accept(node["tag"], state, path.concat(["tag"]));
  // quasi is of types TemplateLiteral
  node["quasi"] = visitor.accept(node["quasi"], state, path.concat(["quasi"]));
  return node;
}
Visitor.prototype.visitAssignmentProperty = function visitAssignmentProperty(node, state, path) {
  var visitor = this;
  // value is of types Pattern, Expression
  node["value"] = visitor.accept(node["value"], state, path.concat(["value"]));
  // key is of types Expression
  node["key"] = visitor.accept(node["key"], state, path.concat(["key"]));
  return node;
}
Visitor.prototype.visitObjectPattern = function visitObjectPattern(node, state, path) {
  var visitor = this;
  // properties is a list with types AssignmentProperty, RestProperty
  var newElements = [];
  for (var i = 0; i < node["properties"].length; i++) {
    var ea = node["properties"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["properties", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["properties"] = newElements;
  return node;
}
Visitor.prototype.visitArrayPattern = function visitArrayPattern(node, state, path) {
  var visitor = this;
  // elements is a list with types Pattern
  if (node["elements"]) {
    var newElements = [];
    for (var i = 0; i < node["elements"].length; i++) {
      var ea = node["elements"][i];
      var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["elements", i])) : ea;
      if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
      else newElements.push(acceptedNodes);
    }
    node["elements"] = newElements;
  }
  return node;
}
Visitor.prototype.visitRestElement = function visitRestElement(node, state, path) {
  var visitor = this;
  // argument is of types Pattern
  node["argument"] = visitor.accept(node["argument"], state, path.concat(["argument"]));
  return node;
}
Visitor.prototype.visitAssignmentPattern = function visitAssignmentPattern(node, state, path) {
  var visitor = this;
  // left is of types Pattern
  node["left"] = visitor.accept(node["left"], state, path.concat(["left"]));
  // right is of types Expression
  node["right"] = visitor.accept(node["right"], state, path.concat(["right"]));
  return node;
}
Visitor.prototype.visitClassExpression = function visitClassExpression(node, state, path) {
  var visitor = this;
  // id is of types Identifier
  if (node["id"]) {
    node["id"] = visitor.accept(node["id"], state, path.concat(["id"]));
  }
  // superClass is of types Expression
  if (node["superClass"]) {
    node["superClass"] = visitor.accept(node["superClass"], state, path.concat(["superClass"]));
  }
  // body is of types ClassBody
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitMetaProperty = function visitMetaProperty(node, state, path) {
  var visitor = this;
  // meta is of types Identifier
  node["meta"] = visitor.accept(node["meta"], state, path.concat(["meta"]));
  // property is of types Identifier
  node["property"] = visitor.accept(node["property"], state, path.concat(["property"]));
  return node;
}
Visitor.prototype.visitImportDeclaration = function visitImportDeclaration(node, state, path) {
  var visitor = this;
  // specifiers is a list with types ImportSpecifier, ImportDefaultSpecifier, ImportNamespaceSpecifier
  var newElements = [];
  for (var i = 0; i < node["specifiers"].length; i++) {
    var ea = node["specifiers"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["specifiers", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["specifiers"] = newElements;
  // source is of types Literal
  node["source"] = visitor.accept(node["source"], state, path.concat(["source"]));
  return node;
}
Visitor.prototype.visitImportSpecifier = function visitImportSpecifier(node, state, path) {
  var visitor = this;
  // imported is of types Identifier
  node["imported"] = visitor.accept(node["imported"], state, path.concat(["imported"]));
  // local is of types Identifier
  node["local"] = visitor.accept(node["local"], state, path.concat(["local"]));
  return node;
}
Visitor.prototype.visitImportDefaultSpecifier = function visitImportDefaultSpecifier(node, state, path) {
  var visitor = this;
  // local is of types Identifier
  node["local"] = visitor.accept(node["local"], state, path.concat(["local"]));
  return node;
}
Visitor.prototype.visitImportNamespaceSpecifier = function visitImportNamespaceSpecifier(node, state, path) {
  var visitor = this;
  // local is of types Identifier
  node["local"] = visitor.accept(node["local"], state, path.concat(["local"]));
  return node;
}
Visitor.prototype.visitExportNamedDeclaration = function visitExportNamedDeclaration(node, state, path) {
  var visitor = this;
  // declaration is of types Declaration
  if (node["declaration"]) {
    node["declaration"] = visitor.accept(node["declaration"], state, path.concat(["declaration"]));
  }
  // specifiers is a list with types ExportSpecifier
  var newElements = [];
  for (var i = 0; i < node["specifiers"].length; i++) {
    var ea = node["specifiers"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["specifiers", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["specifiers"] = newElements;
  // source is of types Literal
  if (node["source"]) {
    node["source"] = visitor.accept(node["source"], state, path.concat(["source"]));
  }
  return node;
}
Visitor.prototype.visitExportSpecifier = function visitExportSpecifier(node, state, path) {
  var visitor = this;
  // exported is of types Identifier
  node["exported"] = visitor.accept(node["exported"], state, path.concat(["exported"]));
  // local is of types Identifier
  node["local"] = visitor.accept(node["local"], state, path.concat(["local"]));
  return node;
}
Visitor.prototype.visitExportDefaultDeclaration = function visitExportDefaultDeclaration(node, state, path) {
  var visitor = this;
  // declaration is of types Declaration, Expression
  node["declaration"] = visitor.accept(node["declaration"], state, path.concat(["declaration"]));
  return node;
}
Visitor.prototype.visitExportAllDeclaration = function visitExportAllDeclaration(node, state, path) {
  var visitor = this;
  // source is of types Literal
  node["source"] = visitor.accept(node["source"], state, path.concat(["source"]));
  return node;
}
Visitor.prototype.visitAwaitExpression = function visitAwaitExpression(node, state, path) {
  var visitor = this;
  // argument is of types Expression
  if (node["argument"]) {
    node["argument"] = visitor.accept(node["argument"], state, path.concat(["argument"]));
  }
  return node;
}
Visitor.prototype.visitRegExpLiteral = function visitRegExpLiteral(node, state, path) {
  var visitor = this;
  return node;
}
Visitor.prototype.visitFunctionDeclaration = function visitFunctionDeclaration(node, state, path) {
  var visitor = this;
  // id is of types Identifier
  node["id"] = visitor.accept(node["id"], state, path.concat(["id"]));
  // params is a list with types Pattern
  var newElements = [];
  for (var i = 0; i < node["params"].length; i++) {
    var ea = node["params"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["params", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["params"] = newElements;
  // body is of types BlockStatement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitVariableDeclaration = function visitVariableDeclaration(node, state, path) {
  var visitor = this;
  // declarations is a list with types VariableDeclarator
  var newElements = [];
  for (var i = 0; i < node["declarations"].length; i++) {
    var ea = node["declarations"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["declarations", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["declarations"] = newElements;
  return node;
}
Visitor.prototype.visitNewExpression = function visitNewExpression(node, state, path) {
  var visitor = this;
  // callee is of types Expression, Super
  node["callee"] = visitor.accept(node["callee"], state, path.concat(["callee"]));
  // arguments is a list with types Expression, SpreadElement
  var newElements = [];
  for (var i = 0; i < node["arguments"].length; i++) {
    var ea = node["arguments"][i];
    var acceptedNodes = ea ? visitor.accept(ea, state, path.concat(["arguments", i])) : ea;
    if (Array.isArray(acceptedNodes)) newElements.push.apply(newElements, acceptedNodes);
    else newElements.push(acceptedNodes);
  }
  node["arguments"] = newElements;
  return node;
}
Visitor.prototype.visitForOfStatement = function visitForOfStatement(node, state, path) {
  var visitor = this;
  // left is of types VariableDeclaration, Pattern
  node["left"] = visitor.accept(node["left"], state, path.concat(["left"]));
  // right is of types Expression
  node["right"] = visitor.accept(node["right"], state, path.concat(["right"]));
  // body is of types Statement
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}
Visitor.prototype.visitClassDeclaration = function visitClassDeclaration(node, state, path) {
  var visitor = this;
  // id is of types Identifier
  node["id"] = visitor.accept(node["id"], state, path.concat(["id"]));
  // superClass is of types Expression
  if (node["superClass"]) {
    node["superClass"] = visitor.accept(node["superClass"], state, path.concat(["superClass"]));
  }
  // body is of types ClassBody
  node["body"] = visitor.accept(node["body"], state, path.concat(["body"]));
  return node;
}

// >>>>>>>>>>>>> END OF AUTO GENERATED CODE >>>>>>>>>>>>>
module.exports = Visitor;
