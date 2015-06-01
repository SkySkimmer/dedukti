open Term

exception NotUnifiable
val resolve : int Basics.LList.t -> typed term -> typed term
