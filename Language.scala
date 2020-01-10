package PLTImplementation

trait Language {
  final case class LanguageException(private val message: String = "",
                                     private val cause: Throwable = None.orNull)
    extends Exception(message, cause)
}