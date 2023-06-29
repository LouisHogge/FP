sealed abstract class PLF // ADT for propositional logic formulas

case class AF(s: String) extends PLF
case class AND(lf: PLF*) extends PLF
case class OR(lf: PLF*) extends PLF
case class IFTHEN(f1: PLF, f2: PLF) extends PLF
case class NOT(f1: PLF) extends PLF
case class NAND(f1: PLF, f2: PLF) extends PLF
case class XOR(f1: PLF, f2: PLF) extends PLF
case class XNOR(f1: PLF, f2: PLF) extends PLF
case class EQUIV(f1: PLF, f2: PLF) extends PLF

object PLF:

    /**
    * Apply alpha-rules and beta-rules on a formula and return a List of the result
    *
    * @param f            PLF (formula to analyze)
    *
    * @return List[List[PLF]] list of list of elimination rule apply on f 
    */
    def eliminationRule(f: PLF): List[List[PLF]] = f match

        // literal set
        case f if isLiteralSet(f) => List(List(f))

        // non literal formulas 

        // XOR = AND(OR(f1, f2), NOT(AND(f1, f2)))
        case XOR(f1,f2) => List(List(f1, NOT(f2)), List(NOT(f1), f2))
        
        // XNOR = NOT(XOR(f1, f2))
        case XNOR(f1,f2) => List(List(f1, f2), List(NOT(f1), NOT(f2)))

        // EQUIV = XNOR
        case EQUIV(f1, f2) => List(List(f1, f2), List(NOT(f1), NOT(f2)))

        // NAND = NOT(AND(f1, f2)) 
        case NAND(f1,f2) => List(List(NOT(f1)), List(NOT(f2)))
        
        // double NOT
        case NOT(NOT(f1)) => List(List(f1))

        // alpha-beta rules

        // alpha-rule 1 - AND with n>=1
        case AND(lf*) => List(lf.toList)
        
        // alpha-rule 2  - OR with n>=1
        case NOT(OR(lf*)) => List(lf.toList.map(x => NOT(x)))
        
        // alpha-rule 3
        case NOT(IFTHEN(f1,f2)) => List(List(f1, NOT(f2)))
        
        // beta-rule 1 - OR with n>=1
        case OR(lf*) => 
            def iter(lf: List[PLF], acc : List[List[PLF]]): List[List[PLF]] = 
                if lf.isEmpty then acc
                else iter(lf.tail, acc ++ List(List(lf.head)))
            iter(lf.toList, Nil)

        // beta-rule 2 - AND with n>=1
        case NOT(AND(lf*)) => 
            def iter(lf: List[PLF], acc : List[List[PLF]]): List[List[PLF]] = 
                if lf.isEmpty then acc
                else iter(lf.tail, acc ++ List(List(NOT(lf.head))))
            iter(lf.toList, Nil)
        
        // beta-rule 3
        case (IFTHEN(f1,f2)) => List(List(NOT(f1)), List(f2))

    /**
    * Say if a formula is literal or not.
    *
    * @param f     PLF (formula to analyze) 
    *
    * @return true/false
    */
    def isLiteralSet(f: PLF): Boolean = f match 
        case AF(_) => true
        case NOT(AF(_)) => true
        case _ => false

    /**
    * Say if a List of formula is literal or not.
    *
    * @param l     List[PLF] (list of formula to analyze) 
    *
    * @return true/false
    */
    def listIsLiteralSet(l: List[PLF]): Boolean = l match
        case Nil => false
        case _ => l.forall(isLiteralSet)

    /**
    * Say if a double List isEmpty. ex: List(List()) == empty
    *
    * @param ll     List[List[A]] (double list) 
    *
    * @return true/false
    */
    def doubleListIsEmpty[A](ll: List[List[A]]): Boolean =
        ll.forall(x => x.isEmpty)

    /**
    * Distribute the element in List l1 in all element of List l2.
    * If one is empty just return the other
    *
    * @param l1     List[List[PLF]] (double list) 
    * @param l2     List[List[PLF]] (double list) 
    *
    * @return l_distrib    List[List[PLF]] (double list distributed) 
    */
    def distributeSet(l1: List[List[PLF]], l2: List[List[PLF]]): List[List[PLF]] =
        if doubleListIsEmpty(l1) then return l2
        if doubleListIsEmpty(l2) then return l1

        @annotation.tailrec
        def in_loop(l1: List[List[PLF]], l2: List[List[PLF]], i: Int, j: Int, acc: List[List[PLF]]): List[List[PLF]] = 
            if j == l2.size then acc
            else 
                val l_cons = l1(i) ::: l2(j)
                in_loop(l1, l2, i, j + 1, l_cons :: acc)

        @annotation.tailrec
        def ext_loop(l1: List[List[PLF]], l2: List[List[PLF]], i: Int, j: Int,  acc: List[List[PLF]]): List[List[PLF]] = 
            if i == l1.size then acc
            else ext_loop(l1, l2, i + 1, j, in_loop(l1, l2, i, j, Nil).concat(acc))

        ext_loop(l1, l2, 0, 0, Nil).reverse

    /**
    * Apply the semantic tableau algorithm on a List of formula
    *
    * @param listPLF list of formula
    * @return list_of_sem_tab   List[List[PLF]] (set of all semantic tableau)
    */
    def semtab(listPLF: List[PLF]): List[List[PLF]] =

        /**
        * Apply elimination rule on a formula and merge the result on a accumulator
        *
        * @param f       PLF (formula to analyze) 
        * @param acc     List[List[PLF]] (accumulator) 
        *
        * @return merg    List[List[PLF]] (each elimination rule result) 
        */
        def merge(acc: List[List[PLF]], f: PLF): List[List[PLF]] =
            eliminationRule(f).flatMap(a => acc.map(b => a.concat(b)))

        /**
        * For each tableau, apply the elimination rule, merge this result 
        * and make this process recursively until all set are literal
        *
        * @param t      List[PLF] (list of formula on wich apply seù) 
        *
        * @return list_of_sem_tab   List[List[PLF]] (set of all semantic tableau) 
        */
        def processPLF(t: List[PLF]): List[List[PLF]] =
            if t.forall(isLiteralSet) then
                List(t)

            @annotation.tailrec
            def loop(t: List[PLF], acc_merg: List[List[PLF]], l_lit: List[List[PLF]]): List[List[PLF]] =

                // all formula has been treated
                if t.isEmpty then
                    l_lit
                
                // acc_merg is totally literal
                else if acc_merg.forall(l => listIsLiteralSet(l)) && !doubleListIsEmpty(acc_merg) then

                    val list_lit = distributeSet(l_lit, acc_merg)

                    loop(t.tail, List(List()), list_lit)
                
                // acc_merg have to be merge another time
                else if !acc_merg.forall(l => listIsLiteralSet(l)) && !doubleListIsEmpty(acc_merg) then

                    val merge_of_merge = acc_merg.map(l => l.foldLeft(List(List.empty: List[PLF]))(merge)).flatten

                    loop(t, merge_of_merge, l_lit)

                // go to the first/next formula and apply merge once on it
                else
                    val t_head = t.head 

                    val merg = merge(List(List.empty: List[PLF]), t_head)

                    loop(t, merg, l_lit)

            loop(t, List(), List())

        processPLF(listPLF)

    /**
    * Verify if a tableau is closed
    *
    * @param fList a tableau
    * @return true/false
    */
    @annotation.tailrec
    def isClosedList(fList: List[PLF]): Boolean = 
        if (fList.isEmpty) false
        else 
            (fList.head match 
                    case AF(_)    => fList.tail.exists( _ == NOT(fList.head))
                    case NOT(AF(a)) => fList.tail.exists( _ == AF(a))
                    case _ => false
            )  || isClosedList(fList.tail)
    
    def isOpenList(fList: List[PLF]): Boolean = !isClosedList(fList)

    /**
    * Say if it exist at least one model for which all the formulas
    * in the List[PLF] are true. 
    *
    * @param hypo the basic List[PLF] on which, it apply semtab() and 
    *             check if there is a open set of formula in it
    * @return true/false
    */
    def isSatisfiable(hypo: List[PLF]): Boolean = 
        semtab(hypo.toList).exists(isOpenList)

    /**
    * Say if we join the set of formula "hypo" and the formula "f" is this satisfiable
    * 
    * @param hypo set of formula
    * @param f formula to analyze
    * @return true/false
    */
    def isValid(hypo: List[PLF], f: PLF): Boolean = !isSatisfiable(hypo.toList :+ NOT(f))
    
    /**
    * Say if the formula is always false
    *
    * @param f formula to evaluate
    * @return true/false
    */
    def isTautology(f: PLF): Boolean = !isSatisfiable(List(NOT(f)))
    
    /**
    * Say if the formula is always true
    *
    * @param f formula to evaluate
    * @return true/false
    */
    def isContradiction(f: PLF): Boolean = !isSatisfiable(List(f))

    /**
    *  Return all open tableaux from a set of hypotheses
    *
    * @param hypo
    * @return open tableaux
    */
    def openLists(hypo: List[PLF]): List[List[PLF]] = 
        @annotation.tailrec
        def iter(sTableaux: List[List[PLF]], acc: List[List[PLF]]): List[List[PLF]] =
            if (sTableaux.isEmpty) then return acc
            else if (isOpenList(sTableaux.head))
                return iter(sTableaux.tail, acc :+ removeDuplicates(sTableaux.head))
            return iter(sTableaux.tail, acc)
        iter(semtab(hypo), Nil)
    
    /**
    * Remove the duplicates in a List
    *
    * @param list list with duplicates
    * @return list with same element sithout their duplicates
    */
    def removeDuplicates(list: List[PLF]): List[PLF] = 
        def remove(l: List[PLF], first: PLF): List[PLF] = 
            if (l.isEmpty) List(first)
            else if (l.contains(first)) remove(l.tail, l.head)
            else remove(l.tail, l.head) :+ first
        if(list.isEmpty) list
        else remove(list.tail, list.head)

    /**
    * Say if the 2 list is the same even if element in it are in different order
    *
    * @param l1 first list to compare
    * @param l2 second list to compare
    * @return true/false
    */
    def haveSameElements[A](l1: List[A], l2: List[A]): Boolean =
        (l1.toSet).equals(l2.toSet)

    /**
    * Delete some element of index i in list
    *
    * @param list to delete element from
    * @param index of element to delete in list
    * @return list without element of index i
    */
    def delete[A](list: List[A], i: Int) = 
        list.take(i) ++ list.drop(i + 1)

    /**
    * Remove duplicated elements in a list
    *
    * @param list to delete duplicates from
    * @return list without duplicates
    */
    def removeDuplicatedList(sTableaux: List[List[PLF]]): List[List[PLF]] = 

        @annotation.tailrec
        def in_loop(l: List[List[PLF]], i: Int, j: Int, acc: List[List[PLF]]): List[List[PLF]] = 
            if j == i then acc
            else 
                if (haveSameElements(l(i), l(j))) then in_loop(l, i-1, 0, delete(acc, i))
                else in_loop(l, i, j + 1, acc)

        @annotation.tailrec
        def ext_loop(l: List[List[PLF]], i: Int, j: Int, acc: List[List[PLF]]): List[List[PLF]] = 
            if i == -1 then acc
            else ext_loop(l, i - 1, j, in_loop(sTableaux, i, j, acc))

        ext_loop(sTableaux, sTableaux.size - 1, 0, sTableaux).reverse

    /**
    * Give all the PLF in the set of formula which are not in the open tableau
    * 
    * @param list
    * @param sTableaux semantic tableau of set of formula
    * @return List of all PLF missing in the open tableau
    */
    def missingPLF(list: List[PLF], sTableaux: List[List[PLF]]): List[PLF] = 

        @annotation.tailrec
        def allPLF(openList: List[PLF], l: List[PLF], acc: List[PLF]): List[PLF] = 
            if (l.isEmpty) return acc
            l.head match
                case AF(a) => {
                    if (!acc.contains(l.head)) 
                        if (!openList.contains(l.head) && !openList.contains(NOT(AF(a))))
                            return allPLF(openList, l.tail, acc :+ l.head)
                        else return allPLF(openList, l.tail, acc)
                    else return allPLF(openList, l.tail, acc)
                }
                case NOT(AF(a)) => {
                    if (!acc.contains(AF(a))) 
                        if (!openList.contains(l.head) && !openList.contains(AF(a)))
                            return allPLF(openList, l.tail, acc :+ AF(a))
                        else return allPLF(openList, l.tail, acc)
                    else return allPLF(openList, l.tail, acc)
                }
                case _ => Nil
        allPLF(list, sTableaux.flatten, Nil)
    
    /**
    * Build all the models from a given tableau and the formulas that don't appear in this tableau
    * 
    * @param missingPLF all the formulas that aren't in the tableau
    * @param openList open tableau from semtab
    * @return List of lists with each list corresponding to a model from the open tableau
    */
    def modelsForAList(missingPLF: List[PLF], openList: List[PLF]): List[List[PLF]] =

        var acc_models :List[List[PLF]] = List()
        def iter(missingPLF: List[PLF], acc: List[PLF]): Unit =

            if (missingPLF.isEmpty)
                acc_models = acc_models :+ acc
            else 
                iter(missingPLF.tail, acc :+ missingPLF.head)
                iter(missingPLF.tail, acc :+ NOT(missingPLF.head))

        iter(missingPLF, openList)
        acc_models

    /**
    * Build all the models based on a set of formulas
    * 
    * @param hypo set of formulas(hypotheses)
    * @return List of lists with each list corresponding to a model. 
    * All the models possible are represented
    */
    def models(hypo: List[PLF]): List[List[PLF]] = 
        val sTableaux = semtab(hypo)
        val openTableaux = openLists(hypo)

        @annotation.tailrec
        def iter(list: List[List[PLF]], models: List[List[PLF]]): List[List[PLF]] = 
            if (list.isEmpty) 
                return models
            else iter(list.tail, models.concat(modelsForAList(missingPLF(list.head, sTableaux), list.head)))
        
        removeDuplicatedList(iter(openTableaux, Nil))

    /**
    * Find all of the counter examples for a formula and a set of hypotheses
    * 
    * @param hypo set of formulas(hypotheses)
    * @param f formula 
    * @return List of lists with each list corresponding to a counter example. 
    * All the counter examples possible are represented
    */
    def counterexamples(hypo: List[PLF], f: PLF): List[List[PLF]] = 
        if (isValid(hypo, f)) return List(List())
        else models(hypo :+ NOT(f))


def main(args : Array[String]): Unit = 
    import PLF._

    // une List() avec une seule formule
    val plf1 = List(IFTHEN(AF("p"), IFTHEN(AF("q"), AF("r"))))

    // une List() avec un set de 2 formules
    val plf2 = List(
                    IFTHEN(AF("p"), IFTHEN(AF("q"), AF("r"))), 
                    NOT(IFTHEN(IFTHEN(AF("p"), AF("q")), AF("r")))
                    )
    
    // une List() avec un set de 3 formules
    val plf3 = List(
                    IFTHEN(AF("p"), IFTHEN(AF("q"), AF("r"))), 
                    NOT(IFTHEN(IFTHEN(AF("p"), AF("q")), AF("r"))), 
                    OR(AF("p"), AF("q"), AF("r"))
                    )

    val semtab3 = semtab(plf3)
    println(semtab3)

    val satis3 = isSatisfiable(plf3)
    println(satis3)

    val valid = isValid(List(AND(AF("p"), AF("q"))), (AF("q")))
    println(valid)

    val tauto = isTautology(OR(AF("p"), NOT(AF("p"))))
    println(tauto)

    val contra = isContradiction(AND(AF("p"), NOT(AF("p"))))
    println(contra)

    val mod = models(List(OR(AND(AF("q"), AF("p")), AND(AF("r"), AF("p")))))
    println(mod)

    val counter = counterexamples(List(AF("c"), AF("d"), OR(AF("a"), AF("b"))), AF("a"))
    println(counter)
