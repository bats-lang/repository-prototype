(* pin-audit [--repository <name>] [--file-tickets] -- run at the root of a checkout of repository-prototype: every
   workflow file of every non-archived repository of the organisation is
   allowlisted by its hash or equals a template (bats-lang/repository-
   prototype#396, keyword: pin-audit). Its exit status is 1 when any file
   fails and 0 otherwise, 2 for arguments it does not take (bats-lang/
   repository-prototype#405). *)

#include "share/atspre_staload.hats"

staload "audit.sats"

implement main0 () = let
  val status = pin_audit_run()
in
  if status = 0 then () else exit_void(status)
end
