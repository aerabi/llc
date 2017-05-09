(* This module is used for defining generic Module Types,
   and then using them by replacing this Module Type by its child,
   declaring the Type T explicitly. *)

Module Type ModuleType.

  Parameter T : Type.

End ModuleType.

(* This is an explicit type. *)

Module Type ModuleNat <: ModuleType.

  Definition T := nat.

End ModuleNat.