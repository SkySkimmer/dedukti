open Term

exception NotUnifiable
val resolve : int Basics.LList.t -> 'a term -> 'a term
