// Type definitions for Mozilla SpiderMonkey Parser API 1.8.5
// Project: https://developer.mozilla.org/en-US/docs/Mozilla/Projects/SpiderMonkey/Parser_API
// Definitions by: vvakame <https://github.com/vvakame/>
// Definitions: https://github.com/borisyankov/DefinitelyTyped

declare module "spiderMonkeyParserAPI" {

    // NOTE if property can hold null, that property to be optional.

    module Syntax {
        /**
         * By default, Reflect.parse() produces Node objects, which are plain JavaScript objects (i.e., their prototype derives from the standard Object prototype).
         * All node types implement the following interface:
         */
        interface Node {
            /**
             * The type field is a string representing the AST variant type.
             * Each subtype of Node is documented below with the specific string of its type field.
             * You can use this field to determine which interface a node implements.
             */
            type: string;
            /**
             * The loc field represents the source location information of the node.
             * If the parser produced no information about the node's source location, the field is null; otherwise it is an object consisting of a start position (the position of the first character of the parsed source region) and an end position (the position of the first character after the parsed source region):
             */
            loc?: SourceLocation;
        }

        interface SourceLocation {
            source?: string;
            start: Position;
            end: Position;
        }

        /**
         * Each Position object consists of a line number (1-indexed) and a column number (0-indexed):
         */
        interface Position {
            line: number;   // uint32 >= 1;
            column: number; // uint32 >= 0;
        }

        /**
         * A complete program source tree.
         */
        interface Program extends Node {
            type: "Program";
            body: Statement[];
        }

        /**
         * A function declaration or expression.
         * The body of the function may be a block statement, or in the case of an expression closure, an expression.
         * If the generator flag is true, the function is a generator function, i.e., contains a yield expression in its body (other than in a nested function).
         * If the expression flag is true, the function is an expression closure and the body field is an expression.
         */
        interface Function extends Node {
            id?: Identifier;
            params: Pattern[];
            defaults: Expression[];
            rest?: Identifier;
            body?: BlockStatement | Expression;
            generator: boolean;
            expression: boolean;
        }

        /**
         * Any statement.
         */
        interface Statement extends Node {
        }

        /**
         * An empty statement, i.e., a solitary semicolon.
         */
        interface EmptyStatement extends Statement {
            type: "EmptyStatement";
        }

        /**
         * A block statement, i.e., a sequence of statements surrounded by braces.
         */
        interface BlockStatement extends Statement {
            type: "BlockStatement";
            body: Statement[];
        }

        interface ExpressionStatement extends Statement {
            type: "ExpressionStatement";
            expression: Expression;
        }

        /**
         * An if statement.
         */
        interface IfStatement extends Statement {
            type: "IfStatement";
            test: Expression;
            consequent: Statement;
            alternate?: Statement;
        }

        /**
         * A labeled statement, i.e., a statement prefixed by a break/continue label.
         */
        interface LabeledStatement extends Statement {
            type: "LabeledStatement";
            label: Identifier;
            body: Statement;
        }

        /**
         * A break statement.
         */
        interface BreakStatement extends Statement {
            type: "BreakStatement";
            label?: Identifier;
        }

        /**
         * A continue statement.
         */
        interface ContinueStatement extends Statement {
            type: "ContinueStatement";
            label?: Identifier;
        }

        /**
         * A with statement.
         */
        interface WithStatement extends Statement {
            type: "WithStatement";
            object: Expression;
            body: Statement;
        }

        /**
         * A switch statement.
         * The lexical flag is metadata indicating whether the switch statement contains any unnested let declarations (and therefore introduces a new lexical scope).
         */
        interface SwitchStatement extends Statement {
            type: "SwitchStatement";
            discriminant: Expression;
            cases: SwitchCase[];
            lexical: boolean;
        }

        /**
         * A return statement.
         */
        interface ReturnStatement extends Statement {
            type: "ReturnStatement";
            argument?: Expression;
        }

        /**
         * A throw statement.
         */
        interface ThrowStatement extends Statement {
            type: "ThrowStatement";
            argument: Expression;
        }

        /**
         * A try statement.
         */
        interface TryStatement extends Statement {
            type: "TryStatement";
            block: BlockStatement;
            handler?: CatchClause;
            guardedHandlers: CatchClause[];
            finalizer?: BlockStatement;
        }

        /**
         * A while statement.
         */
        interface WhileStatement extends Statement {
            type: "WhileStatement";
            test: Expression;
            body: Statement;
        }

        /**
         * A do/while statement.
         */
        interface DoWhileStatement extends Statement {
            type: "DoWhileStatement";
            body: Statement;
            test: Expression;
        }

        /**
         * A for statement.
         */
        interface ForStatement extends Statement {
            type: "ForStatement";
            init?: VariableDeclaration | Expression;
            test?: Expression;
            update?: Expression;
            body: Statement;
        }

        /**
         * A for/in statement, or, if each is true, a for each/in statement.
         */
        interface ForInStatement extends Statement {
            type: "ForInStatement";
            left: VariableDeclaration | Expression;
            right: Expression;
            body: Statement;
            each: boolean;
        }

        /**
         * A for/of statement.
         */
        interface ForOfStatement extends Statement {
            type: "ForOfStatement";
            left: VariableDeclaration | Expression;
            right: Expression;
            body: Statement;
        }

        /**
         * A let statement.
         */
        interface LetStatement extends Statement {
            type: "LetStatement";
            head: VariableDeclarator[];
            body: Statement;
        }

        /**
         * A debugger statement.
         */
        interface DebuggerStatement extends Statement {
            type: "DebuggerStatement";
        }

        /**
         * Any declaration node. Note that declarations are considered statements; this is because declarations can appear in any statement context in the language recognized by the SpiderMonkey parser.
         */
        interface Declaration extends Statement {
        }

        /**
         * A function declaration.
         */
        interface ClassDeclaration extends Declaration {
            type: "ClassDeclaration";
            id: Identifier; // Note: The id field cannot be null.
        }

        /**
         * A function declaration.
         */
        interface FunctionDeclaration extends Function, Declaration {
            type: "FunctionDeclaration";
            id: Identifier; // Note: The id field cannot be null.
            params: Pattern[];
            defaults: Expression[];
            rest?: Identifier;
            body: BlockStatement | Expression;
            generator: boolean;
            expression: boolean;
        }

        /**
         * A variable declaration, via one of var, let, or const.
         */
        interface VariableDeclaration extends Declaration {
            type: "VariableDeclaration";
            declarations: VariableDeclarator[];
            kind: string; // "var" | "let" | "const";
        }

        /**
         * A variable declarator.
         */
        interface VariableDeclarator extends Node {
            type: "VariableDeclarator";
            id: Pattern; // Note: The id field cannot be null.
            init?: Expression;
        }

        /**
         * Any expression node.
         * Since the left-hand side of an assignment may be any expression in general, an expression can also be a pattern.
         */
        interface Expression extends Node, Pattern {
        }

        /**
         * A this expression.
         */
        interface ThisExpression extends Expression {
            type: "ThisExpression";
        }

        /**
         * An array expression.
         */
        interface ArrayExpression extends Expression {
            type: "ArrayExpression";
            elements: Expression[]; // [ Expression | null ];
        }

        /**
         * An object expression.
         */
        interface ObjectExpression extends Expression {
            type: "ObjectExpression";
            properties: Property[];
        }

        /**
         * A literal property in an object expression can have either a string or number as its value.
         * Ordinary property initializers have a kind value "init"; getters and setters have the kind values "get" and "set", respectively.
         */
        interface Property extends Node {
            type: "Property";
            key: Literal | Identifier;
            value: Expression;
            kind: "init" | "get" | "set";
        }

        /**
         * A function expression.
         */
        interface FunctionExpression extends Function, Expression {
            type: "FunctionExpression";
            id?: Identifier;
            params: Pattern[];
            defaults: Expression[];
            rest?: Identifier;
            body: BlockStatement | Expression;
            generator: boolean;
            expression: boolean;
        }

        /**
         * A fat arrow function expression, i.e., `let foo = (bar) => { ... body ... }`.
         */
        interface ArrowExpression extends Function, Expression {
            type: "ArrowExpression";
            params: Pattern[];
            defaults: Expression[];
            rest?: Identifier;
            body: BlockStatement | Expression;
            generator: boolean;
            expression: boolean;
        }

        /**
         * A sequence expression, i.e., a comma-separated sequence of expressions.
         */
        interface SequenceExpression extends Expression {
            type: "SequenceExpression";
            expressions: Expression[];
        }

        /**
         * A unary operator expression.
         */
        interface UnaryExpression extends Expression {
            type: "UnaryExpression";
            operator: UnaryOperator;
            prefix: boolean;
            argument: Expression;
        }

        /**
         * A binary operator expression.
         */
        interface BinaryExpression extends Expression {
            type: "BinaryExpression";
            operator: BinaryOperator;
            left: Expression;
            right: Expression;
        }

        /**
         * An assignment operator expression.
         */
        interface AssignmentExpression extends Expression {
            type: "AssignmentExpression";
            operator: AssignmentOperator;
            left: Expression;
            right: Expression;
        }

        /**
         * An update (increment or decrement) operator expression.
         */
        interface UpdateExpression extends Expression {
            type: "UpdateExpression";
            operator: UpdateOperator;
            argument: Expression;
            prefix: boolean;
        }

        /**
         * A logical operator expression.
         */
        interface LogicalExpression extends Expression {
            type: "LogicalExpression";
            operator: LogicalOperator;
            left: Expression;
            right: Expression;
        }

        /**
         * A conditional expression, i.e., a ternary ?/: expression.
         */
        interface ConditionalExpression extends Expression {
            type: "ConditionalExpression";
            test: Expression;
            alternate: Expression;
            consequent: Expression;
        }

        /**
         * A new expression.
         */
        interface NewExpression extends Expression {
            type: "NewExpression";
            callee: Expression;
            arguments: Expression[];
        }

        /**
         * A function or method call expression.
         */
        interface CallExpression extends Expression {
            type: "CallExpression";
            callee: Expression;
            arguments: Expression[];
        }

        /**
         * A member expression.
         * If computed === true, the node corresponds to a computed e1[e2] expression and property is an Expression.
         * If computed === false, the node corresponds to a static e1.x expression and property is an Identifier.
         */
        interface MemberExpression extends Expression {
            type: "MemberExpression";
            object: Expression;
            property: Identifier | Expression;
            computed: boolean;
        }

        /**
         * A yield expression.
         */
        interface YieldExpression extends Expression {
            type: "YieldExpression";
            argument?: Expression;
        }

        /**
         * An array comprehension.
         * The blocks array corresponds to the sequence of for and for each blocks.
         * The optional filter expression corresponds to the final if clause, if present.
         */
        interface ComprehensionExpression extends Expression {
            type: "ComprehensionExpression";
            body: Expression;
            blocks: ComprehensionBlock[];
            filter?: Expression;
        }

        /**
         * A generator expression.
         * As with array comprehensions, the blocks array corresponds to the sequence of for and for each blocks, and the optional filter expression corresponds to the final if clause, if present.
         */
        interface GeneratorExpression extends Expression {
            type: "GeneratorExpression";
            body: Expression;
            blocks: ComprehensionBlock[];
            filter?: Expression;
        }

        /**
         * A graph expression, aka "sharp literal," such as #1={ self: #1# }.
         */
        interface GraphExpression extends Expression {
            type: "GraphExpression";
            index: number; // uint32;
            expression: Literal;
        }

        /**
         * A graph index expression, aka "sharp variable," such as #1#.
         */
        interface GraphIndexExpression extends Expression {
            type: "GraphIndexExpression";
            index: number; // uint32;
        }

        /**
         * A let expression.
         */
        interface LetExpression extends Expression {
            type: "LetExpression";
            head: VariableDeclarator[];
            body: Expression;
        }

        /**
         * JavaScript 1.7 introduced destructuring assignment and binding forms.
         * All binding forms (such as function parameters, variable declarations, and catch block headers) accept array and object destructuring patterns in addition to plain identifiers.
         * The left-hand sides of assignment expressions can be arbitrary expressions, but in the case where the expression is an object or array literal, it is interpreted by SpiderMonkey as a destructuring pattern.
         *
         * Since the left-hand side of an assignment can in general be any expression, in an assignment context, a pattern can be any expression.
         * In binding positions (such as function parameters, variable declarations, and catch headers), patterns can only be identifiers in the base case, not arbitrary expressions.
         */
        interface Pattern extends Node {
        }

        /**
         * An object-destructuring pattern. A literal property in an object pattern can have either a string or number as its value.
         */
        interface ObjectPattern extends Pattern {
            type: "ObjectPattern";
            properties: {key: Literal | Identifier; value: Pattern;}[]; // [ { key: Literal | Identifier, value: Pattern } ];
        }

        /**
         * An array-destructuring pattern.
         */
        interface ArrayPattern extends Pattern {
            type: "ArrayPattern";
            elements: Pattern[]; // [ Pattern | null ];
        }

        /**
         * A case (if test is an Expression) or default (if test === null) clause in the body of a switch statement.
         */
        interface SwitchCase extends Node {
            type: "SwitchCase";
            test?: Expression;
            consequent: Statement[];
        }

        /**
         * A catch clause following a try block.
         * The optional guard property corresponds to the optional expression guard on the bound variable.
         */
        interface CatchClause extends Node {
            type: "CatchClause";
            param: Pattern;
            guard?: Expression;
            body: BlockStatement;
        }

        /**
         * A for or for each block in an array comprehension or generator expression.
         */
        interface ComprehensionBlock extends Node {
            type: "ComprehensionBlock";
            left: Pattern;
            right: Expression;
            each: boolean;
        }

        /**
         * An identifier.
         * Note that an identifier may be an expression or a destructuring pattern.
         */
        interface Identifier extends Node, Expression, Pattern {
            type: "Identifier";
            name: string;
        }

        /**
         * A literal token. Note that a literal can be an expression.
         */
        interface Literal extends Node, Expression {
            type: "Literal";
            value?: string | boolean | number | RegExp;
        }

        /**
         * A unary operator token.
         */
        type UnaryOperator = "-" | "+" | "!" | "~" | "typeof" | "void" | "delete";

        /**
         * A binary operator token.
         */
        type BinaryOperator =
             "==" | "!=" | "===" | "!=="
                  | "<" | "<=" | ">" | ">="
                  | "<<" | ">>" | ">>>"
                  | "+" | "-" | "*" | "/" | "%"
                  | "|" | "^" | "&" | "in"
                  | "instanceof";

        /**
         * A logical operator token.
         */
        type LogicalOperator = "||" | "&&";

        /**
         * An assignment operator token.
         */
        type AssignmentOperator = "=" | "+=" | "-=" | "*=" | "/=" | "%="
                                | "<<=" | ">>=" | ">>>="
                                | "|=" | "^=" | "&=";

        /**
         * An update (increment or decrement) operator token.
         */
        type UpdateOperator = "++" | "--";
    }
}
