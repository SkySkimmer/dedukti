open Term

exception NotUnifiable
val resolve : int Basic.LList.t -> 'a term -> 'a term
