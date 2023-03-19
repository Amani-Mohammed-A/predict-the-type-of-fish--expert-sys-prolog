;;;======================================================
;;;   fish Identification Expert System
;;;
;;;     A simple expert system which attempts to identify
;;;     an fish based on its characteristics.
;;;     The knowledge base in this example is a 
;;;     collection of facts which represent backward
;;;     chaining rules. CLIPS forward chaining rules are
;;;     then used to simulate a backward chaining inference
;;;     engine.
;;;
;;;     CLIPS Version 6.0 Example
;;; 
;;;     To execute, merely load, reset, and run.
;;;     Answer questions yes or no.
;;;======================================================

;;;***************************
;;;* DEFTEMPLATE DEFINITIONS *
;;;***************************

(deftemplate rule 
   (multislot if)
   (multislot then))

;;;**************************
;;;* INFERENCE ENGINE RULES *
;;;**************************

(defrule propagate-goal ""
   (goal is ?goal)
   (rule (if ?variable $?)
         (then ?goal ? ?value))
   =>
   (assert (goal is ?variable)))

(defrule goal-satified ""
   (declare (salience 30))
   ?f <- (goal is ?goal)
   (variable ?goal ?value)
   (answer ? ?text ?goal)
   =>
   (retract ?f)
   (format t "%s%s%n" ?text ?value))

(defrule remove-rule-no-match ""
   (declare (salience 20))
   (variable ?variable ?value)
   ?f <- (rule (if ?variable ? ~?value $?))
   =>
   (retract ?f))

(defrule modify-rule-match ""
   (declare (salience 20))
   (variable ?variable ?value)
   ?f <- (rule (if ?variable ? ?value and $?rest))
   =>
   (modify ?f (if ?rest)))

(defrule rule-satisfied ""
   (declare (salience 20))
   (variable ?variable ?value)
   ?f <- (rule (if ?variable ? ?value)
               (then ?goal ? ?goal-value))
   =>
   (retract ?f)
   (assert (variable ?goal ?goal-value)))

(defrule ask-question-no-legalvalues ""
   (declare (salience 10))
   (not (legalanswers $?))
   ?f1 <- (goal is ?variable)
   ?f2 <- (question ?variable ? ?text)
   =>
   (retract ?f1 ?f2)
   (format t "%s " ?text)
   (assert (variable ?variable (read))))

(defrule ask-question-legalvalues ""
   (declare (salience 10))
   (legalanswers ? $?answers)
   ?f1 <- (goal is ?variable)
   ?f2 <- (question ?variable ? ?text)
   =>
   (retract ?f1)
   (format t "%s " ?text)
   (printout t ?answers " ")
   (bind ?reply (read))
   (if (member (lowcase ?reply) ?answers) 
     then (assert (variable ?variable ?reply))
          (retract ?f2)
     else (assert (goal is ?variable))))

;;;***************************
;;;* DEFFACTS KNOWLEDGE BASE *
;;;***************************

(deffacts knowledge-base 
   (goal is type.fish)

   (legalanswers are yes no)

   (rule (if backbone is yes) 
         (then skeleton is backbone))
   (rule (if backbone is no) 
         (then skeleton is jellyback))
   (question backbone is "Does your fish have a backbone?")
   
   (rule (if skeleton is backbone and
          Caudal.fin.to.the.tip.of.the.tail   is yes) 
         (then fin is diphycercal))
   (rule (if skeleton is backbone and
          Caudal.fin.to.the.tip.of.the.tail   is no) 
         (then fin is heterocercal))
   (question Caudal.fin.to.the.tip.of.the.tail   is " cadual fin Vertebrae extend to the tip of the tail?")
   
   (rule (if skeleton is jellyback and
          live.prime.in.water is  yes) 
         (then fin is water ))
   (rule (if skeleton is jellyback and
          live.prime.in.water is  no) 
         (then fin is elsewhere))
   (question live.prime.in.water is  "Does your fish live just in water ?")
   (rule (if fin is diphycercal and
          has.gills is yes) 
         (then class is gills))
   (rule (if fin is diphycercal and
          has.gills is no) 
         (then type.fish is granddad))
   (question has.gills is "Normally, does your fish have gill?")
   (rule (if fin is heterocercal and
          always.in.land is yes) 
         (then class is land))
   (rule (if fin is heterocercal and
          always.in.land is no) 
         (then class is wwater))
   (question always.in.land is "Is your fish sometimes in land?")
   (rule (if fin is water and
          flat.bodied is yes) 
         (then type.fish is squid))
   (rule (if fin is water and
          flat.bodied is no) 
         (then type.fish is scorpaena))
   (question flat.bodied is "Does your fish have a flat body?")
   (rule (if fin is elsewhere and
          body.long is yes) 
         (then class is longbody))
   (rule (if fin is elsewhere and
          body.long is no) 
         (then class is amphibious))
   (question body.long is "Is the fishs body is long?")
   (rule (if class is gills and
          can.eat.meat is yes) 
         (then order is meat))
   (rule (if class is gills and
          can.eat.meat is no) 
         (then order is vegy))
   (question can.eat.meat is "Does your fish eat white meat?")
   (rule (if class is land and
          pore is yes) 
         (then type.fish is Mudskipper ))
   (rule (if class is land and
          pore is no) 
         (then type.fish is jump_eyed_fish/Walking_catfish))
   (question pore is "Does your fish have a pore in his body?")
   (rule (if class is wwater and
          rough is yes) 
         (then type.fish is puffer_fish))
   (rule (if class is wwater and
          rough is no) 
         (then order is soft))
   (question rough is "Is your fish covered with rough skin?")
   (rule (if class is longbody and
          foureye is yes) 
         (then order is jum))
   (rule (if class is longbody and
          foureye is no) 
         (then type.fish is tripod_fish ))
   (question foureye is "Does your fish have a four eye?")
   (rule (if class is amphibious and
          short.body  is yes) 
         (then order is short))
   (rule (if class is amphibious and
          short.body  is no) 
         (then order is notshort))
   (question short.body  is "Does your fish your fish short?")
   (rule (if order is meat and
          fly is yes) 
         (then type.fish is exocoetidae))
   (rule (if order is meat and
          fly is no) 
         (then type.fish is wader))
   (question fly is "Can your fish fly?")
   (rule (if order is vegy and
          algae is yes) 
         (then family is algae))
   (rule (if order is vegy and
          algae is no) 
         (then family is white_meet))
   (question algae is "Does your fish eat algae?")
   (rule (if order is soft and
          jump is yes) 
         (then type.fish is shark))
   (rule (if order is soft and
          jump is no) 
         (then type.fish is coral_rout))
   (question jump is "Does your fish jump?")
   (rule (if order is jum and
          tail is yes) 
         (then type.fish is dasyatidae))
   (rule (if order is jum and
          tail is no) 
         (then type.fish is parrot_fish))
   (question tail is "Does your fish have a tail?")
   (rule (if order is short and
          attach  is yes) 
         (then family is attach ))
   (rule (if order is short and
          attach  is no) 
         (then type.fish is tilapia_aurea))
   (question attach  is "Is your fish attached with other fish?")
   (rule (if order is notshort and
          thin  is yes) 
         (then type.fish is frilled_shark ))
   (rule (if order is notshort and
          thin  is no) 
         (then type.fish is rhincodon_typus))
   (question thin  is "Is your fish thin?")
   (rule (if family is algae and
          two.toes is yes) 
         (then swim is bladder))
   (rule (if family is algae and
          two.toes is no) 
         (then type.fish is anableps))
   (question two.toes is "Does your fish have two eyes and eat algae ?")
   (rule (if family is white_meet and
          live.in.land is yes) 
         (then swim is water))
   (rule (if family is white_meet and
          live.in.land is no) 
         (then swim is wwater))
   (question live.in.land is "Does your fish live in fresh  water?")
   (rule (if family is attach  and
          pipettes  is yes) 
         (then type.fish is remora))
   (rule (if family is attach  and
          pipettes  is no) 
         (then type.fish is petromyzontiformes))
   (question pipettes  is "Does your fish normally have pipettes  in its body?")
  
   (rule (if swim is bladder and
          sticky_body is yes) 
         (then type.fish is salmon))
   (rule (if swim is bladder and
          sticky_body is no) 
         (then type.fish is lamprey))
   (question sticky_body is "Does your fish have bladder?")
   (rule (if swim is water and
          hunted is yes) 
         (then type.fish is white_shark))
   (rule (if swim is water and
          hunted is no) 
         (then type.fish is dolphin/porpoise))
   (question hunted is "Is your fish commercially hunted?")
   (rule (if swim is wwater and
          front.teeth is yes) 
         (then species is teeth))
   (rule (if swim is wwater and
          front.teeth is no) 
         (then type.fish is mola_mola_fish))
 (question front.teeth is "Does your fish have large mouth?")
   (rule (if species is teeth and
          large.teeth is yes) 
         (then type.fish is alligator_gar))
(rule (if species is teeth and
   large.teeth is no)
        (then type.fish is glit_head_bream))
   (question large.teeth is "Does your fish have large teeths?")
   (answer is "I think your fish is a " type.fish))

