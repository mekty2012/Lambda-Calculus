package PLTImplementation

package object extends Language {
  trait HoareLogic
  case class PartialCorrectness(p:PredicateLogic.PredicateLogic, c:SimpleImperativeLanguage.SimpleImperativeLanguage, q:PredicateLogic.PredicateLogic) extends HoareLogic
  case class TotalCorrectness(p:PredicateLogic.PredicateLogic, c:SimpleImperativeLanguage.SimpleImperativeLanguage, q:PredicateLogic.PredicateLogic) extends HoareLogic

}