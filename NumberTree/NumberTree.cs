using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Linq.Expressions;

namespace test
{
    /// <summary>
    /// 
    /// </summary>
    class NumberTree
    {
        class Generator
        {
            public readonly decimal[] Sources = 
            {
                1,
                3, 
                4, 
                6, 
            };

            private readonly ExpressionType[] _operationTypes =
            {
                ExpressionType.Add, 
                ExpressionType.Subtract, 
                ExpressionType.Multiply, 
                ExpressionType.Divide, 
            };

            class Snapshot
            {
                public Expression Tree;
                public Expression ActiveSite;
                public List<decimal> AvailableConstants;
            }

            public Dictionary<decimal, List<Expression>> Results = new Dictionary<decimal, List<Expression>>();

            public int IterationCount { get; private set; }

            private HashSet<int> Compiled = new HashSet<int>();

            public void Iterate()
            {
                var stack = new Stack<Snapshot>();

                //seed stack with constant roots

                foreach (var constant in Sources)
                {

                    var ss = new Snapshot
                    {
                        Tree = Expression.Constant(constant),
                        AvailableConstants = new List<decimal>(Sources.Where(c => c != constant))
                    };

                    ss.ActiveSite = ss.Tree;

                    stack.Push(ss);
                }

                //expand tree

                while (stack.Count != 0)
                {
                    IterationCount++;

                    var snapshot = stack.Pop();

                    var evaluationHashVisitor = new EvaluationHashVisitor();
                    evaluationHashVisitor.Visit(snapshot.Tree);

                    if (!snapshot.AvailableConstants.Any())
                    {
                        decimal val;

                        if (Compiled.Contains(evaluationHashVisitor.Hash))
                            continue;

                        Compiled.Add(evaluationHashVisitor.Hash);

                        try
                        {
                            val = Expression.Lambda<Func<decimal>>(snapshot.Tree).Compile()();
                        }
                        catch (DivideByZeroException)
                        {
                            continue;
                        }

                        List<Expression> list;

                        val = Math.Abs(decimal.Round(val, 4));

                        if (!Results.TryGetValue(val, out list))
                        {
                            list = new List<Expression>();
                            Results[val] = list;
                        }

                        list.Add(snapshot.Tree);

                        continue;
                    }


                    //some constants left, so expand
                    foreach (var constant in snapshot.AvailableConstants)
                    {
                        foreach (var expressionType in _operationTypes)
                        {
                            for (int direction = 0; direction < 2; direction++)
                            {
                                //dont spawn excessive b*a variant if spawned a*b
                                if (direction != 0 && (expressionType == ExpressionType.Multiply || expressionType == ExpressionType.Add))
                                    continue;

                                var spawn = new Snapshot();

                                var vtor = new ExpandConstExpressionVisitor(snapshot.ActiveSite,
                                    expressionType,
                                    constant,
                                    direction == 0);

                                spawn.Tree = vtor.Visit(snapshot.Tree);
                                spawn.ActiveSite = vtor.ActiveSite;
                                spawn.AvailableConstants = new List<decimal>(snapshot.AvailableConstants.Where(ac => ac != constant));

                                stack.Push(spawn);
                            }
                        }
                    }
                }
            }
        }


        /// <summary>
        /// 
        /// </summary>
        public class EvaluationHashVisitor : ExpressionVisitor
        {
            public int Hash { get; private set; }

            #region Stats

            public int DivisionVisitCount { get; private set; }
            public int MultiplyVisitCount { get; private set; }
            public int AddVisitCount { get; private set; }
            public int SubtractVisitCount { get; private set; }

            #endregion

            private bool _canIgnoreSign = false;

            /* note about decimal.GetHashCode 
             * from https://github.com/dotnet/coreclr/blob/master/src/classlibnative/bcltype/decimal.cpp
             * 
                 conversion to double is lossy and produces rounding errors so we mask off the lowest 4 bits
                 
                 For example these two numerically equal decimals with different internal representations produce
                 slightly different results when converted to double:
                
                 decimal a = new decimal(new int[] { 0x76969696, 0x2fdd49fa, 0x409783ff, 0x00160000 });
                                     => (decimal)1999021.176470588235294117647000000000 => (double)1999021.176470588
                 decimal b = new decimal(new int[] { 0x3f0f0f0f, 0x1e62edcc, 0x06758d33, 0x00150000 }); 
                                     => (decimal)1999021.176470588235294117647000000000 => (double)1999021.1764705882
                
             * 
                return ((((int *)&dbl)[0]) & 0xFFFFFFF0) ^ ((int *)&dbl)[1];
              
             * Noting that:
             * a) -1*n ^ -2 == 1*n ^ 2,
             * b) ExpressionVisitor walks in execution order
             * 
             * hashes for identical expressions like -1 * -3 == 1 * 3 could be made
             * equal, but we should avoid making 1+3 == -1-3 equal
             */
            protected override Expression VisitConstant(ConstantExpression node)
            {
                var d = (decimal)node.Value;

                unchecked
                {
                    if (!_canIgnoreSign)
                        d = d > 0 ? d : d * 17;

                    Hash *= 3;
                    Hash ^= d.GetHashCode();
                }

                return base.VisitConstant(node);
            }

            protected override Expression VisitBinary(BinaryExpression node)
            {
                unchecked
                {
                    Hash *= 3;
                    Hash ^= node.NodeType.GetHashCode();
                }

                _canIgnoreSign = node.NodeType == ExpressionType.Multiply || node.NodeType == ExpressionType.Divide;

                switch (node.NodeType)
                {
                    case ExpressionType.Divide:
                        DivisionVisitCount++;
                        break;

                    case ExpressionType.Multiply:
                        MultiplyVisitCount++;
                        break;

                    case ExpressionType.Add:
                        AddVisitCount++;
                        break;

                    case ExpressionType.Subtract:
                        SubtractVisitCount++;
                        break;



                }

                return base.VisitBinary(node);
            }
        }

        /// <summary>
        /// Replaces target expression with binary operation
        /// </summary>
        class ExpandConstExpressionVisitor : ExpressionVisitor
        {
            private readonly Expression _target;
            private readonly ExpressionType _operation;
            private readonly decimal _parameter;
            private readonly bool _useAsRight;

            public Expression ActiveSite;

            public ExpandConstExpressionVisitor(Expression target, ExpressionType operation, Decimal parameter, bool UseAsRight)
            {
                _target = target;
                _operation = operation;
                _parameter = parameter;
                _useAsRight = UseAsRight;
            }

            public override Expression Visit(Expression expression)
            {
                if (expression != _target)
                    return base.Visit(expression);

                ActiveSite = _useAsRight ? Expression.MakeBinary(_operation, expression, Expression.Constant(_parameter)) :
                    Expression.MakeBinary(_operation, Expression.Constant(_parameter), expression);

                return ActiveSite;
            }

        }

        /// <summary>
        /// Based on http://stackoverflow.com/a/17018229
        /// </summary>
        /// <param name="num"></param>
        /// <param name="epsilon"></param>
        /// <param name="maxIterations"></param>
        /// <returns></returns>
        public static string DecimalToFraction(decimal num, decimal epsilon = 0.0001m, int maxIterations = 20)
        {
            decimal[] d = new decimal[maxIterations + 2];
            d[1] = 1;

            bool sig = num < 0;

            num = Math.Abs(num);

            decimal z = num;
            decimal n = 1;
            int t = 1;

            if (Math.Abs(num - Math.Truncate(num)) < epsilon)
                return num.ToString(CultureInfo.CurrentCulture);

            while (t < maxIterations && Math.Abs(n / d[t] - num) > epsilon)
            {
                t++;
                z = 1 / (z - Math.Truncate(z));
                d[t] = d[t - 1] * Math.Truncate(z) + d[t - 2];
                n = Math.Round(num * d[t]);
            }


            return string.Format("{2}{0}/{1}", n, d[t], sig ? "-" : "");
        }

        private static void Main(string[] args)
        {
            var gen = new Generator();
            gen.Iterate();

            var rz = gen.Results.OrderBy(p => Math.Abs(p.Key - Math.Round(p.Key))).ThenBy(p => p.Value.Count);

            Console.WriteLine("Completed in {0} iterations", gen.IterationCount);

            using (var fw = File.CreateText("numbers.html"))
            {
                fw.WriteLine("<h1>Possible combinations for {0}</h1>",string.Join(",&nbsp;",gen.Sources));


                fw.WriteLine("<table>");
                fw.WriteLine("<tr><td>#</td><td>expressions</td></tr>");

                foreach (var item in rz)
                {
                    fw.WriteLine("<tr>");
                    fw.Write("<td>");
                    fw.WriteLine("{0,3} results for {1}:", item.Value.Count, DecimalToFraction(item.Key));
                    fw.Write("</td>");
                    fw.Write("<td style='border-bottom: 1px solid black'>");
                    foreach (var expression in item.Value)
                    {
                        var vc = new EvaluationHashVisitor();

                        vc.Visit(expression);

                        fw.WriteLine("{0,20} [{1}]<br/>", expression, vc.DivisionVisitCount);

                    }
                    fw.Write("</td>");
                    fw.Write("</tr>");
                }

                fw.Write("</table>");
            }






        }
    }
}

