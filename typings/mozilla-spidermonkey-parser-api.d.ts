// Type definitions for Mozilla SpiderMonkey Parser API 1.8.5
// Project: https://developer.mozilla.org/en-US/docs/Mozilla/Projects/SpiderMonkey/Parser_API
// Definitions by: vvakame <https://github.com/vvakame/>
// Definitions: https://github.com/borisyankov/DefinitelyTyped

declare module "spiderMonkeyParserAPI" {

    // NOTE if property can hold null, that property to be optional.

    module Syntax {

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
        interface Program {
            type: "Program";
            body: Statement[];
            loc?: SourceLocation;
        }

        /**
         * Any statement.
         */
        type Statement = EmptyStatement
                       | BlockStatement
                       | ExpressionStatement
                       | IfStatement
                       | LabeledStatement
                       | BreakStatement
                       | ContinueStatement
                       | WithStatement
                       | SwitchStatement
                       | ReturnStatement
                       | ThrowStatement
                       | TryStatement
                       | WhileStatement
                       | DoWhileStatement
                       | ForStatement
                       | ForInStatement
                       | ForOfStatement
                       | LetStatement
                       | DebuggerStatement
                       | VariableDeclaration
                       | ClassDeclaration
                       | FunctionDeclaration

        /**
         * An empty statement, i.e., a solitary semicolon.
         */
        interface EmptyStatement {
            type: "EmptyStatement";
            loc?: SourceLocation;
        }

        /**
         * A block statement, i.e., a sequence of statements surrounded by braces.
         */
        interface BlockStatement {
            type: "BlockStatement";
            body: Statement[];
            loc?: SourceLocation;
        }

        interface ExpressionStatement {
            type: "ExpressionStatement";
            expression: Expression;
            loc?: SourceLocation;
        }

        /**
         * An if statement.
         */
        interface IfStatement {
            type: "IfStatement";
            test: Expression;
            consequent: Statement;
            alternate?: Statement;
            loc?: SourceLocation;
        }

        /**
         * A labeled statement, i.e., a statement prefixed by a break/continue label.
         */
        interface LabeledStatement {
            type: "LabeledStatement";
            label: Identifier;
            body: Statement;
            loc?: SourceLocation;
        }

        /**
         * A break statement.
         */
        interface BreakStatement {
            type: "BreakStatement";
            label?: Identifier;
            loc?: SourceLocation;
        }

        /**
         * A continue statement.
         */
        interface ContinueStatement {
            type: "ContinueStatement";
            label?: Identifier;
            loc?: SourceLocation;
        }

        /**
         * A with statement.
         */
        interface WithStatement {
            type: "WithStatement";
            object: Expression;
            body: Statement;
            loc?: SourceLocation;
        }

        /**
         * A switch statement.
         * The lexical flag is metadata indicating whether the switch statement contains any unnested let declarations (and therefore introduces a new lexical scope).
         */
        interface SwitchStatement {
            type: "SwitchStatement";
            discriminant: Expression;
            cases: SwitchCase[];
            lexical: boolean;
            loc?: SourceLocation;
        }

        /**
         * A return statement.
         */
        interface ReturnStatement {
            type: "ReturnStatement";
            argument?: Expression;
            loc?: SourceLocation;
        }

        /**
         * A throw statement.
         */
        interface ThrowStatement {
            type: "ThrowStatement";
            argument: Expression;
            loc?: SourceLocation;
        }

        /**
         * A try statement.
         */
        interface TryStatement {
            type: "TryStatement";
            block: BlockStatement;
            handler?: CatchClause;
            guardedHandlers: CatchClause[];
            finalizer?: BlockStatement;
            loc?: SourceLocation;
        }

        /**
         * A while statement.
         */
        interface WhileStatement {
            type: "WhileStatement";
            test: Expression;
            body: Statement;
            loc?: SourceLocation;
        }

        /**
         * A do/while statement.
         */
        interface DoWhileStatement {
            type: "DoWhileStatement";
            body: Statement;
            test: Expression;
            loc?: SourceLocation;
        }

        /**
         * A for statement.
         */
        interface ForStatement {
            type: "ForStatement";
            init?: VariableDeclaration | Expression;
            test?: Expression;
            update?: Expression;
            body: Statement;
            loc?: SourceLocation;
        }

        /**
         * A for/in statement, or, if each is true, a for each/in statement.
         */
        interface ForInStatement {
            type: "ForInStatement";
            left: VariableDeclaration | Expression;
            right: Expression;
            body: Statement;
            each: boolean;
            loc?: SourceLocation;
        }

        /**
         * A for/of statement.
         */
        interface ForOfStatement {
            type: "ForOfStatement";
            left: VariableDeclaration | Expression;
            right: Expression;
            body: Statement;
            loc?: SourceLocation;
        }

        /**
         * A let statement.
         */
        interface LetStatement {
            type: "LetStatement";
            head: VariableDeclarator[];
            body: Statement;
            loc?: SourceLocation;
        }

        /**
         * A debugger statement.
         */
        interface DebuggerStatement {
            type: "DebuggerStatement";
            loc?: SourceLocation;
        }

        /**
         * A function declaration.
         */
        interface ClassDeclaration {
            type: "ClassDeclaration";
            id: Identifier; // Note: The id field cannot be null.
            loc?: SourceLocation;
        }

        /**
         * A function declaration.
         */
        interface FunctionDeclaration {
            type: "FunctionDeclaration";
            id: Identifier; // Note: The id field cannot be null.
            params: Pattern[];
            defaults?: Expression[];
            rest?: Identifier;
            body: BlockStatement | Expression;
            generator: boolean;
            expression: boolean;
            loc?: SourceLocation;
        }

        /**
         * A variable declaration, via one of var, let, or const.
         */
        interface VariableDeclaration {
            type: "VariableDeclaration";
            declarations: VariableDeclarator[];
            kind: string; // "var" | "let" | "const";
            loc?: SourceLocation;
        }

        /**
         * A variable declarator.
         */
        interface VariableDeclarator {
            type: "VariableDeclarator";
            id: Pattern; // Note: The id field cannot be null.
            init?: Expression;
            loc?: SourceLocation;
        }

        export type Expression = ThisExpression
                               | ArrayExpression
                               | ObjectExpression
                               | FunctionExpression
                               | ArrowExpression
                               | SequenceExpression
                               | UnaryExpression
                               | BinaryExpression
                               | AssignmentExpression
                               | UpdateExpression
                               | LogicalExpression
                               | ConditionalExpression
                               | NewExpression
                               | CallExpression
                               | MemberExpression
                               | YieldExpression
                               | ComprehensionExpression
                               | GeneratorExpression
                               | GraphExpression
                               | GraphIndexExpression
                               | LetExpression
                               | Identifier
                               | Literal;

        /**
         * A this expression.
         */
        interface ThisExpression {
            type: "ThisExpression";
            loc?: SourceLocation;
        }

        /**
         * An array expression.
         */
        interface ArrayExpression {
            type: "ArrayExpression";
            elements: Expression[]; // [ Expression | null ];
            loc?: SourceLocation;
        }

        /**
         * An object expression.
         */
        interface ObjectExpression {
            type: "ObjectExpression";
            properties: Property[];
            loc?: SourceLocation;
        }

        /**
         * A literal property in an object expression can have either a string or number as its value.
         * Ordinary property initializers have a kind value "init"; getters and setters have the kind values "get" and "set", respectively.
         */
        interface Property {
            type: "Property";
            key: Literal | Identifier;
            value: Expression;
            kind: "init" | "get" | "set";
            loc?: SourceLocation;
        }

        /**
         * A function expression.
         */
        interface FunctionExpression {
            type: "FunctionExpression";
            id?: Identifier;
            params: Pattern[];
            defaults?: Expression[];
            rest?: Identifier;
            body: BlockStatement | Expression;
            generator: boolean;
            expression: boolean;
            loc?: SourceLocation;
        }

        /**
         * A fat arrow function expression, i.e., `let foo = (bar) => { ... body ... }`.
         */
        interface ArrowExpression {
            type: "ArrowExpression";
            params: Pattern[];
            defaults?: Expression[];
            rest?: Identifier;
            body: BlockStatement | Expression;
            generator: boolean;
            expression: boolean;
            loc?: SourceLocation;
        }

        /**
         * A sequence expression, i.e., a comma-separated sequence of expressions.
         */
        interface SequenceExpression {
            type: "SequenceExpression";
            expressions: Expression[];
            loc?: SourceLocation;
        }

        /**
         * A unary operator expression.
         */
        interface UnaryExpression {
            type: "UnaryExpression";
            operator: UnaryOperator;
            prefix: boolean;
            argument: Expression;
            loc?: SourceLocation;
        }

        /**
         * A binary operator expression.
         */
        interface BinaryExpression {
            type: "BinaryExpression";
            operator: BinaryOperator;
            left: Expression;
            right: Expression;
            loc?: SourceLocation;
        }

        /**
         * An assignment operator expression.
         */
        interface AssignmentExpression {
            type: "AssignmentExpression";
            operator: AssignmentOperator;
            left: Expression;
            right: Expression;
            loc?: SourceLocation;
        }

        /**
         * An update (increment or decrement) operator expression.
         */
        interface UpdateExpression {
            type: "UpdateExpression";
            operator: UpdateOperator;
            argument: Expression;
            prefix: boolean;
            loc?: SourceLocation;
        }

        /**
         * A logical operator expression.
         */
        interface LogicalExpression {
            type: "LogicalExpression";
            operator: LogicalOperator;
            left: Expression;
            right: Expression;
            loc?: SourceLocation;
        }

        /**
         * A conditional expression, i.e., a ternary ?/: expression.
         */
        interface ConditionalExpression {
            type: "ConditionalExpression";
            test: Expression;
            alternate: Expression;
            consequent: Expression;
            loc?: SourceLocation;
        }

        /**
         * A new expression.
         */
        interface NewExpression {
            type: "NewExpression";
            callee: Expression;
            arguments: Expression[];
            loc?: SourceLocation;
        }

        /**
         * A function or method call expression.
         */
        interface CallExpression {
            type: "CallExpression";
            callee: Expression;
            arguments: Expression[];
            loc?: SourceLocation;
        }

        /**
         * A member expression.
         * If computed === true, the node corresponds to a computed e1[e2] expression and property is an Expression.
         * If computed === false, the node corresponds to a static e1.x expression and property is an Identifier.
         */
        interface MemberExpression {
            type: "MemberExpression";
            object: Expression;
            property: Identifier | Expression;
            computed: boolean;
            loc?: SourceLocation;
        }

        /**
         * A yield expression.
         */
        interface YieldExpression {
            type: "YieldExpression";
            argument?: Expression;
            loc?: SourceLocation;
        }

        /**
         * An array comprehension.
         * The blocks array corresponds to the sequence of for and for each blocks.
         * The optional filter expression corresponds to the final if clause, if present.
         */
        interface ComprehensionExpression {
            type: "ComprehensionExpression";
            body: Expression;
            blocks: ComprehensionBlock[];
            filter?: Expression;
            loc?: SourceLocation;
        }

        /**
         * A generator expression.
         * As with array comprehensions, the blocks array corresponds to the sequence of for and for each blocks, and the optional filter expression corresponds to the final if clause, if present.
         */
        interface GeneratorExpression {
            type: "GeneratorExpression";
            body: Expression;
            blocks: ComprehensionBlock[];
            filter?: Expression;
            loc?: SourceLocation;
        }

        /**
         * A graph expression, aka "sharp literal," such as #1={ self: #1# }.
         */
        interface GraphExpression {
            type: "GraphExpression";
            index: number; // uint32;
            expression: Literal;
            loc?: SourceLocation;
        }

        /**
         * A graph index expression, aka "sharp variable," such as #1#.
         */
        interface GraphIndexExpression {
            type: "GraphIndexExpression";
            index: number; // uint32;
            loc?: SourceLocation;
        }

        /**
         * A let expression.
         */
        interface LetExpression {
            type: "LetExpression";
            head: VariableDeclarator[];
            body: Expression;
            loc?: SourceLocation;
        }

        /**
         * JavaScript 1.7 introduced destructuring assignment and binding forms.
         * All binding forms (such as function parameters, variable declarations, and catch block headers) accept array and object destructuring patterns in addition to plain identifiers.
         * The left-hand sides of assignment expressions can be arbitrary expressions, but in the case where the expression is an object or array literal, it is interpreted by SpiderMonkey as a destructuring pattern.
         *
         * Since the left-hand side of an assignment can in general be any expression, in an assignment context, a pattern can be any expression.
         * In binding positions (such as function parameters, variable declarations, and catch headers), patterns can only be identifiers in the base case, not arbitrary expressions.
         */
        export type Pattern = ObjectPattern
                            | ArrayPattern
                            | Identifier;

        /**
         * An object-destructuring pattern. A literal property in an object pattern can have either a string or number as its value.
         */
        interface ObjectPattern {
            type: "ObjectPattern";
            properties: {key: Literal | Identifier; value: Pattern;}[]; // [ { key: Literal | Identifier, value: Pattern } ];
            loc?: SourceLocation;
        }

        /**
         * An array-destructuring pattern.
         */
        interface ArrayPattern {
            type: "ArrayPattern";
            elements: Pattern[]; // [ Pattern | null ];
            loc?: SourceLocation;
        }

        /**
         * A case (if test is an Expression) or default (if test === null) clause in the body of a switch statement.
         */
        interface SwitchCase {
            type: "SwitchCase";
            test?: Expression;
            consequent: Statement[];
            loc?: SourceLocation;
        }

        /**
         * A catch clause following a try block.
         * The optional guard property corresponds to the optional expression guard on the bound variable.
         */
        interface CatchClause {
            type: "CatchClause";
            param: Pattern;
            guard?: Expression;
            body: BlockStatement;
            loc?: SourceLocation;
        }

        /**
         * A for or for each block in an array comprehension or generator expression.
         */
        interface ComprehensionBlock {
            type: "ComprehensionBlock";
            left: Pattern;
            right: Expression;
            each: boolean;
            loc?: SourceLocation;
        }

        /**
         * An identifier.
         * Note that an identifier may be an expression or a destructuring pattern.
         */
        interface Identifier {
            type: "Identifier";
            name: string;
            loc?: SourceLocation;
        }

        /**
         * A literal token. Note that a literal can be an expression.
         */
        interface Literal {
            type: "Literal";
            value?: string | boolean | number | RegExp;
            loc?: SourceLocation;
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
