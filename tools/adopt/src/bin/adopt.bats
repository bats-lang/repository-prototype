(* adopt [--only NAME] TEMPLATE COMMIT COMMENT NAME#TICKET... -- adopts a template of
   tools/pin-audit/templates in repositories of the organisation, one draft pull
   request for each (bats-lang/repository-prototype#607). Run at the root of a
   checkout of repository-prototype. Its exit status is 1 when a repository is
   refused or failed and 0 otherwise, 2 for arguments it does not take. *)

#include "share/atspre_staload.hats"

staload "adopt.sats"

implement main0 () = let
  val status = adopt_run()
in
  if status = 0 then () else exit_void(status)
end
