package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * Michael Gohde
   * 
   * Partner: Josh
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */
  
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => s.toDouble
      case Function(_, _, _) => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case Function(_, _, _) => true
      case S(s) => s.length()!=0
      case N(n) => n != 0 && n != -0 && n != Double.NaN
      case _ => false //Undefined values in JavaScript are considered false//??? // delete this line when done
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
      case Undefined => "undefined"
      case N(n) => n.toString()
      case B(b) => b.toString()
      case _ => "" //Use a safe default
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (N(a), N(b)) => bop match {
        case Lt => a<b
        case Le => a<=b
        case Gt => a>b
        case Ge => a>=b
      }
        // Todo: implement this for strings.
      //case _ => ??? // delete this line when done
      case _ => false
    }
  }

  //TODO: Actually start using inequalityVal

  def doMathBin(func: (Double, Double) => Double, e1: Expr, e2: Expr): Expr = {
    val d1=toNumber(e1)
    val d2=toNumber(e2)

    N(func(d1, d2))
  }

  def doBinAnd(e1: Expr, e2: Expr): Expr = {
    val b1=toBoolean(e1)
    val b2=toBoolean(e2)

    //Fun fact: In JavaScript, if two numbers are anded together and are both not equal to 0, the last
    //value is returned. So, if x=5 and y=10, x&&y==10
    //For logical or, the first value is returned:
    //x||y==5

    if(e1.isInstanceOf[N] && e2.isInstanceOf[N]) {
      if(b1 && b2) e2 else if(!b1) e1 else if (!b2) e2 else B(false)
    } else if(e1.isInstanceOf[N]) {
      if(b1 && b2) e1 else if(!b1) e1 else B(false)
    } else if(e2.isInstanceOf[N]) {
      if(b1 && b2) e2 else if(!b2) e2 else B(false)
    } else {
      B(b1 && b2)
    }
  }

  def doBinOr(e1: Expr, e2: Expr): Expr = {
    val b1=toBoolean(e1)
    val b2=toBoolean(e2)

    //Fun fact: In JavaScript, if two numbers are anded together and are both not equal to 0, the last
    //value is returned. So, if x=5 and y=10, x&&y==10
    //For logical or, the first value is returned:
    //x||y==5

    if(e1.isInstanceOf[N] && e2.isInstanceOf[N]) {
      if(b1 || b2) e2 else B(false)
    } else if(e1.isInstanceOf[N]) {
      if(b1 || b2) e1 else if(!b1) e1 else B(false)
    } else if(e2.isInstanceOf[N]) {
      if(b1 || b2) e2 else if(!b2) e2 else B(false)
    } else {
      B(b1 || b2)
    }
  }

  def doCmpBin(func: (Double, Double) =>  Boolean, e1: Expr, e2: Expr): Boolean = {
    try
    {
      val d1=toNumber(e1)
      val d2=toNumber(e2)

      func(d1, d2)
    } catch {
      case e: NumberFormatException => false
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */
  
  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => try{lookup(env, x)} catch { case ex: NoSuchElementException => Undefined}
      
      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

        // ****** Your cases here

        //TODO: update this with new ops.
      case Binary(bop, e1, e2) => bop match
      {
        case Plus => {
          val ee1=eval(env, e1)
          val ee2=eval(env, e2)

          (ee1, ee2) match {
            case (S(a), S(b)) => S(a+b)
            case _ => doMathBin((a: Double, b: Double) => a+b, ee1, ee2)
          }
        }

        case Minus => {
          val ee1=eval(env, e1)
          val ee2=eval(env, e2)

          doMathBin((a: Double, b:Double) => a-b, ee1, ee2)
        }

        case Times => {
          val ee1=eval(env, e1)
          val ee2=eval(env, e2)

          doMathBin((a: Double, b: Double) => a*b, ee1, ee2)
        }

        case Div => {
          val ee1=eval(env, e1)
          val ee2=eval(env, e2)

          doMathBin((a: Double, b:Double) => a/b, ee1, ee2)
        }

        case And => doBinAnd(eval(env, e1), eval(env, e2))
        case Or => doBinOr(eval(env, e1), eval(env, e2))

        case Eq => {
          val ee1=eval(env, e1)
          val ee2=eval(env, e2)

          (ee1, ee2) match {
            case (S(a), S(b)) => B(a==b)
            case (N(a), N(b)) => B(a==b)
            case (B(a), B(b)) => B(a==b)
            case _ => {
              Undefined
            }
          }
        }

        case _ => B(inequalityVal(bop, e1, e2))

        //case Eq => inequalityVal()
        //case Ne => B(doCmpBin((a: Double, b: Double) => (a != b), eval(env, e1), eval(env, e2)))
        //case Lt => B(doCmpBin((a: Double, b: Double) => (a < b), eval(env, e1), eval(env, e2)))
        //case Le => B(doCmpBin((a: Double, b: Double) => (a <= b), eval(env, e1), eval(env, e2)))
        //case Gt => B(doCmpBin((a: Double, b: Double) => (a > b), eval(env, e1), eval(env, e2)))
        //case Ge => B(doCmpBin((a: Double, b: Double) => (a >= b), eval(env, e1), eval(env, e2)))


        case Seq => {eval(env, e1)
          eval(env, e2)}

        case _ => Undefined
      }

      case Unary(uop, e1) => uop match {
        case Not => eval(env, e1) match
        {
          case B(b) => B(!b)
          case _ => Undefined
        }
        case Neg => eval(env, e1) match
        {
          case N(n) => N(-n)
          case _ => Undefined
        }

        case _ => Undefined
      }

        //Update to handle functions better:
      case ConstDecl(x, e1, e2) => {
        val ee1=eval(env, e1)
        val newEnv=extend(env, x, ee1)
        eval(newEnv, e2)
      }

      case If(e1, e2, e3) => {
        if(toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)
      }

      case Call(e1, e2) => {
        val ee1=eval(env, e1)
        val ee2=eval(env, e2)

        //The first argument to Call is a function definition. The second should be its parameter.
        ee1 match {
          // The first string allows us to recurse given a function name
          //The second string allows us to set a parameter
          //The third value is the expression with which we evaluate this function.
          //We need to extend the environment with the parameter.
          case Function(fname: Option[String], fparam, fe1) => fname match{
            case Some(fn) => {
              val newEnv=extend(extend(env, fn, ee1), fparam, ee2)
              eval(newEnv, fe1)
            }
            case None => {
              val newEnv=extend(env, fparam, ee2)
              eval(newEnv, fe1)
            }
          }

          case _ => {
            //Add better handling code
            Undefined
          }
        }

        //Add implementation for specific features like recursion
        //Note: recursion should differ from regular function calls in how we handle environments.
      }
      case _ => Undefined // delete this line when done
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        //case _ => loop(substitute())
      }
    }
    loop(e0, 0)
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => {
        uop match {
          case Neg => {
            e1 match {
              case N(a) => N(-a)
            }
          }

          case Not => {
            e1 match {
              case B(b) => B(!b)
            }
          }
        }
      }
      case Binary(bop, e1, e2) => ???
      case If(e1, e2, e3) => ???
      case Call(e1, e2) => ???
      case Var(y) => ???
      case Function(None, y, e1) => ???
      case Function(Some(y1), y2, e1) => ???
      case ConstDecl(y, e1, e2) => ???
    }
  }
    
  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      
        // ****** Your cases here
      
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      
        // ****** Your cases here

      case Unary(uop, e1) => {
        uop match {
          case Neg => e1 match {
            case N(n) => N(-n)
          }
        }
      }

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}
