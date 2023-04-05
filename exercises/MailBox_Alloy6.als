var sig Message {}
var sig Trash in Message {}

pred delete[m: Message] {
    m not in Trash
    Trash' = Trash + m
    Message' = Message
}

pred restore[m: Message] {
    m in Trash
    Trash' = Trash - m
    Message' = Message
}

pred empty {​
    some Trash​
    no Trash'​
    Message' = Message - Trash​
}​
​
pred donothing {​
    Message' = Message​
    Trash' = Trash​
}​
​
pred restoreEnabled[m:Message] {​
    m in Trash​
}​

fact Behaviour {
    no Trash
    always {
        (some m: Message | delete[m] or restore[m]) or empty or do_nothing
    }
} 

run {}

assert restoreAfterDelete {
    always (all m : Message | restore[m] implies once delete[m])
}

check restoreAfterDelete for 10 steps
check restoreAfterDelete for 1.. steps

assert deleteAll {
    always ((Message in Trash and empty) implies after always no Message)
}

check deleteAll

check MessagesNeverIncreases {
    always (Message' in Message and #Message' = #Message)
}

check IfNotDeletedMessagesNotEmpty {
  (always all m : Message | not delete[m]) implies always not empty
}

// a deleted message can still be restored if the trash is not empty
assert restoreIsPossibleBeforeEmpty {
    always (all m:Message | delete[m]              implies after ((empty or restore[m])              releases restoreEnabled[m]))
}

check restoreIsPossibleBeforeEmpty for 3 but 1.. steps
