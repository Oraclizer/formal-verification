theory Response_Code_Extension_Input
  imports Response_Code_Allocation
begin

definition sync_response_operation :: response_operation where
  "sync_response_operation = (Wire_State_Sync,7)"

definition sync_response_allocations :: response_allocations where
  "sync_response_allocations =
    [(29,Recorded_Result,True,[sync_response_operation]),
     (39,Recorded_Result,False,[sync_response_operation]),
     (40,Recorded_Result,False,[sync_response_operation]),
     (41,Recorded_Result,False,[sync_response_operation])]"

end
