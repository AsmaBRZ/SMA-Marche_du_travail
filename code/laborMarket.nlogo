extensions [matrix]
breed [ persons person];
breed [ companies company];
globals[matchings unemployeds offers Us Vs current-Us meanDiff ]


persons-own[state skills salary location productivity ask-sent];
companies-own[state skills salary location offer-sent];



to start
  set Us []
  set Vs []
  if model-param[
    set-param
  ]
  let i 0
  let U0 n-persons
  let V0 n-companies
  show Us
  while [i < nb-increment][
    let j 0
    while [j < nb-increment][
      let x U0 + i * U-increment
      let y V0 + j * V-increment


      show x
      show y
      episode x y
      show i
      show j
      set j j + 1
    ]
    set i i + 1

  ]
end
to set-param
  set nb-increment 4
  set U-increment 100
  set V-increment 100
  set n-persons 100
  set n-companies 100
  set productivity-threshold-fired 0.5
  set threshold-matching 1.5
  set unexpected-fired 0.1
  set unexpected-company-motivation 0.1
  set unexpected-worker-motivation 0.1
  set n-match 20
  set min-salary-com 0
  set min-salary-ump 0
  set exceptionnal-matching 0.05
end
to go
  while[ length current-Us < 10 or meanDiff > 0.01][
    offer-job
    search-job
    send-prod
    evaluate-emp
    match
    compute-stability-model
    tick
  ]
  let u length unemployeds
  set u u / n-persons
  let v length offers
  set v v / n-persons

  set Us lput u Us
  set Vs lput v Vs
  show Us
  show Vs
  do-plots
end


to compute-stability-model
  let U length unemployeds
  set U U / n-persons
  set current-Us lput U current-Us
  if length current-Us >= 10 [
    if length current-Us > 10[
      set current-Us remove-item 0 current-Us
    ]
    let diffUs []
    let i 0
    while [ i < length current-Us - 1][
      let element1 item i current-Us
      let element2 item 9 current-Us
      set diffUs lput abs ( element1 - element2 ) diffUs
      set meanDiff sum diffUs / length diffUs
      set i i + 1
    ]
  ]

end

to do-plots
  let m 0
  set-current-plot "Beveridge curve"
  set-current-plot-pen "pen-0"
  while [m < length Us ]
    [plotxy item m Us item m Vs
    set m m + 1]
 end


to episode [u v]
  clear-all-plots
  clear-patches
  clear-turtles
  setup-patches
  set unemployeds []
  set offers []
  set matchings []
  set n-persons u
  set n-companies v
  create-persons n-persons [
                      let x random-xcor
                      let y random-ycor
                      setxy  x y
                      set state "unemployed"
                      set skills (list (random 2) (random 2) (random 2) (random 2) (random 2))
                      set ask-sent false
                      set salary min-salary-ump + random 1

                      set location (list (x) (y) )
                      set productivity random-float 1
  ]
  create-companies n-companies [ let x random-xcor
                        let y random-ycor
                        setxy  x y
                        set state "vacant"
                        set skills (list (random 2) (random 2) (random 2) (random 2) (random 2))
                        set location  (list (x) (y) )
                        set offer-sent false
                        set salary min-salary-com + random 1

  ]
  ask persons [ set shape "person"
                set size 2
                set color red
                 ]
  ask companies [ set shape "factory"
                  set size 2
                  set color blue
                  ]
  init-offers
  init-unemployeds
  set current-Us []
  reset-ticks
  go
end

to-report similarity[u o x]
  let sim 0
  let sim-skills  0
  let skillsU 0
  let skillsO 0
  let salaryU 0
  let salaryO 0
  let locationU []
  let locationO []
  let sim-location 0
  let sim-salary 0
  let uAgent one-of turtles with [who = u]
  let oAgent one-of turtles with [who = o]
  ask oAgent[
              set skillsO skills
  ]
  ask uAgent[
              set skillsU skills
  ]
  ;; compute skills similarity
  let i 0
  while [i < 5][
    let skill-o item i skillsO
    let skill-u item i skillsU
    set sim-skills  sim-skills + abs ( skill-o - skill-u )
    set i i + 1
  ]
  set sim-skills 1 - ( sim-skills / 5)

  ;; compute salary similarity
  ask oAgent[
              set salaryO salary
  ]
  ask uAgent[
              set salaryU salary
  ]

  ifelse x = 0[
    ifelse salaryU <= salaryO[
      set sim-salary 1
    ][
      set sim-salary 1 - ( (salaryU - salaryO) / salaryU )
    ]
  ][
    ifelse salaryO <= salaryU[
      set sim-salary 1
    ][
      set sim-salary 1 - ( (salaryO - salaryU) / salaryO )
    ]
  ]


  ;; compute location similarity
  ask uAgent[
              set locationU location
  ]
  ask oAgent[
              set locationO location
  ]
  set sim-location ( ( item 0 locationO - item 0 locationU ) ^ 2 + ( item 1 locationO - item 1 locationU ) ^ 2 ) ^ 0.5

  set sim-location sim-location / ( ( 2 * max-pxcor ) ^ 2 +  ( 2 * max-pycor ) ^ 2 ) ^ 0.5
  set sim-location 1 - sim-location
  if sim-location < 0 [
    set sim-location 0
  ]
  set sim sim-skills + sim-salary + sim-location

  report sim
end
to match

  let nb-hire 0
  ;;show "-------------begin"
  let old-n-match n-match
  let N n-match

  let n-offers length offers
  let n-unemployeds length unemployeds

  ;;define the number of the matches to realize
  let new-n-match (list n-offers n-unemployeds N)
  set N min new-n-match
  let n-seekers  N

  ;; pick up a limited pairs of unemployeds and offers
  let tmp-unemployeds n-of N unemployeds
  let tmp-offers n-of N offers

  ;;show "tmp-unemployeds"
  ;;show tmp-unemployeds
  ;;show "tmp-offers"
  ;;show tmp-offers

  let  similarities []
  let i 0
  let j 0

  while [i < N ] ;; loop on offers
    [
    ;; for each offer, compute the best future employee
    set j 0
    set  similarities []
    ;;show "begin compute matrix of similarities"
    while [j < n-seekers ] ;; loop on unemployed
    [
      let sim-uo similarity item j tmp-unemployeds item i tmp-offers 0
      let sim-ou similarity item j tmp-unemployeds item i tmp-offers 1
      let rand-uo random-float 1
      let rand-ou random-float 1
      if rand-uo < unexpected-worker-motivation [
        ifelse sim-uo > 2 [
          set sim-uo 3
        ][
          set sim-uo sim-uo + 1
        ]
      ]
      if rand-ou < unexpected-company-motivation [
        ifelse sim-ou > 2 [
          set sim-ou 3
        ][
          set sim-ou sim-ou + 1
        ]
      ]
      let similar ( sim-uo + sim-ou ) / 2
      ;;show similar
      set similarities lput similar similarities
      set j j + 1
    ]
    ;;show "end compute matric similarities"

    ;; compute the max similarity to choose the best future employee for the current offer i
    let sim-max-value max similarities
    let index-employee-round position sim-max-value similarities

    let best-seeker item index-employee-round tmp-unemployeds

    let agent-employee one-of persons with [who = best-seeker]

    let agent-company one-of companies with [who = i]
    let rand-exception random-float 1
    if sim-max-value > threshold-matching or rand-exception < exceptionnal-matching
    [ ;; define a random productivity
      set nb-hire nb-hire + 1
      let init-productivity random-float 1
      let index-company item i tmp-offers

      let new-match ( list  index-company best-seeker init-productivity )

      set-filled index-company
      set-hired best-seeker
      set matchings lput new-match matchings
      ;;show "new maaaaarch"
      ;;show new-match
      ;;show index-employee-round
      ;;show i

      set tmp-unemployeds remove-item  index-employee-round tmp-unemployeds
      set tmp-offers remove-item i tmp-offers

      set index-company position index-company offers
      set offers remove-item index-company offers

      set best-seeker position best-seeker unemployeds
      set unemployeds remove-item best-seeker unemployeds


      set N N - 1
      set n-seekers n-seekers - 1
      ;;show "matchhhhhhhhhhhhh"
      ;;show  "tmp-unemployeds"
      ;;show tmp-unemployeds
      ;;show "tmp-offers"
      ;;show tmp-offers
     ]

    set i i + 1
  ]

  set-current-plot "Hire rate"
  set-current-plot-pen "Hire rate"
  plot 100 * (nb-hire / n-unemployeds)
  set n-match old-n-match
  ;;show "---------------end"
end
to offer-job
  ask companies [
    if state = "vacant" and offer-sent = false[
        set offers lput who offers
        set offer-sent true
    ]
  ]
end
to evaluate-emp
  let n-unemployeds length unemployeds
  let nb-fire 0
  ask companies [
  if state = "filled" [
    let i 0
    let N length matchings
    while [ i < N ][
      let tmp-match item i matchings
      let employee-id item 1 tmp-match
      let company-id item 0 tmp-match
      let prod item 2 tmp-match
      ifelse company-id = who [
        let random-unexpected-fired random-float 1
        ifelse  prod < productivity-threshold-fired or random-unexpected-fired <  unexpected-fired [

            ;;employee is fired
            set-fired employee-id
            set-vacant company-id
            set nb-fire nb-fire + 1
            set matchings remove-item i matchings
            set N length matchings
            set i 0
          ][
            set i i + 1
          ]
        ][
          set i i + 1]
      ]
    ]
  ]
  set-current-plot "Fire rate"
  set-current-plot-pen "Fire rate"
  let temp-nb-fire 0
  if n-persons - n-unemployeds > 0 [
    set temp-nb-fire nb-fire / (n-persons - n-unemployeds)
  ]
  plot 100 * temp-nb-fire
end
to search-job
  ask persons [
    if ask-sent = false [
      set unemployeds lput who unemployeds
      set ask-sent true
    ]
  ]
end
to send-prod

  ask persons [
    if state = "employed" [

      let productivity-fluctuation random-float 2 * max-productivity-fluctuation
      set productivity-fluctuation productivity-fluctuation - max-productivity-fluctuation
      let i 0
      let N length matchings
      while [ i < N ][
        let tmp-match item i matchings
        let company-id item 0 tmp-match
        let employee-id item 1 tmp-match
        let old-prod item 2 tmp-match
        if employee-id = who [
          let new-productivity 0
          ifelse old-prod + productivity-fluctuation > 1[
            set new-productivity 1
          ][
            ifelse old-prod + productivity-fluctuation < 0[
              set new-productivity 0
            ][
              set new-productivity old-prod + productivity-fluctuation
            ]
          let new-match (list company-id employee-id new-productivity)
          set matchings replace-item i matchings new-match
          ]
        ]
        set i i + 1
      ]
    ]
  ]
end
to set-hired [i]
   ask persons [
    if who = i [
      set state "employed"
      set color green
    ]
  ]
end
to set-fired[i]
   ask persons [
    if who = i [
      set state "unemployed"
      set unemployeds lput who unemployeds
      set color red
    ]
  ]
end
to set-filled[i]
   ask companies [
    if who = i [
      set state "filled"
      set color pink
    ]
  ]
end
to set-vacant[i]
   ask companies [
    if who = i [
      set state "vacant"
      set color blue
      set offers lput who offers
    ]
  ]
end
to setup-patches
  ask patches [ set pcolor black ]
end
to-report matrix-add-row [matrix row-added]
  let temp-list matrix:to-row-list matrix ;; converts the matrix to a list
  set temp-list lput row-added temp-list ;; the new row is added to the list
  report matrix:from-row-list temp-list ;; converts the list back to a matrix

end
to init-unemployeds
  ask persons [
    if state = "unemployed"[
      set unemployeds lput who unemployeds
      set ask-sent true
    ]
  ]
end
to init-offers
    ask companies [
    if state = "vacant"[
      set offers lput who offers
      set offer-sent true
    ]
  ]
end
@#$#@#$#@
GRAPHICS-WINDOW
477
271
727
522
-1
-1
5.90244
1
10
1
1
1
0
1
1
1
-20
20
-20
20
1
1
1
ticks
30.0

BUTTON
60
10
126
43
NIL
start
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
220
61
392
94
n-match
n-match
0
1000
20.0
1
1
NIL
HORIZONTAL

SLIDER
18
132
190
165
n-companies
n-companies
0
1000
400.0
1
1
NIL
HORIZONTAL

SLIDER
18
88
190
121
n-persons
n-persons
0
1000
400.0
1
1
NIL
HORIZONTAL

SLIDER
14
174
214
207
productivity-threshold-fired
productivity-threshold-fired
0
1
0.5
0.1
1
NIL
HORIZONTAL

PLOT
1175
19
1547
265
Matchings
NIL
NIL
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 0 -5298144 true "" "plot length matchings"

PLOT
788
16
1149
239
Unemployed  rate -Vacancy rate
time
pourcentage
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"Vacancy rate" 1.0 0 -14439633 true "" "plot (length offers / n-persons) * 100"
"Unemployed rate" 1.0 0 -2064490 true "" "plot (length unemployeds / n-persons) * 100"

SLIDER
5
218
198
251
threshold-matching
threshold-matching
0
3
1.5
0.1
1
NIL
HORIZONTAL

SLIDER
218
193
400
226
U-increment
U-increment
1
100
100.0
1
1
NIL
HORIZONTAL

SLIDER
224
239
396
272
V-increment
V-increment
0
100
100.0
1
1
NIL
HORIZONTAL

SLIDER
224
286
396
319
nb-increment
nb-increment
1
10
4.0
1
1
NIL
HORIZONTAL

PLOT
447
10
780
260
Beveridge curve
U
V
0.0
1.0
0.0
4.0
false
true
"" ""
PENS
"pen-0" 1.0 2 -16050907 true "" ""

SLIDER
18
345
192
378
unexpected-fired
unexpected-fired
0
1
0.1
0.1
1
NIL
HORIZONTAL

SLIDER
218
107
390
140
min-salary-ump
min-salary-ump
0
100
0.0
1
1
NIL
HORIZONTAL

SLIDER
219
151
391
184
min-salary-com
min-salary-com
0
100
0.0
1
1
NIL
HORIZONTAL

SWITCH
39
47
166
80
model-param
model-param
1
1
-1000

SLIDER
0
391
232
424
unexpected-company-motivation
unexpected-company-motivation
0
0.5
0.1
0.05
1
NIL
HORIZONTAL

SLIDER
2
436
227
469
unexpected-worker-motivation
unexpected-worker-motivation
0
1
0.1
0.05
1
NIL
HORIZONTAL

SLIDER
5
259
209
292
max-productivity-fluctuation
max-productivity-fluctuation
0
1
0.3
0.1
1
NIL
HORIZONTAL

SLIDER
11
303
190
336
exceptionnal-matching
exceptionnal-matching
0
1
0.05
0.01
1
NIL
HORIZONTAL

PLOT
790
271
1151
462
Hire rate
time
pourcentage
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"Hire rate" 1.0 0 -13345367 true "" ""

PLOT
1177
272
1540
464
Fire rate
time
pourcentage
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"Fire rate" 1.0 0 -2674135 true "" ""

BUTTON
223
10
311
43
NIL
set-param
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

@#$#@#$#@
## WHAT IS IT?

(a general understanding of what the model is trying to show or explain)

## HOW IT WORKS

(what rules the agents use to create the overall behavior of the model)

## HOW TO USE IT

(how to use the model, including a description of each of the items in the Interface tab)

## THINGS TO NOTICE

(suggested things for the user to notice while running the model)

## THINGS TO TRY

(suggested things for the user to try to do (move sliders, switches, etc.) with the model)

## EXTENDING THE MODEL

(suggested things to add or change in the Code tab to make the model more complicated, detailed, accurate, etc.)

## NETLOGO FEATURES

(interesting or unusual features of NetLogo that the model uses, particularly in the Code tab; or where workarounds were needed for missing features)

## RELATED MODELS

(models in the NetLogo Models Library and elsewhere which are of related interest)

## CREDITS AND REFERENCES

(a reference to the model's URL on the web if it has one, as well as any other necessary credits, citations, and links)
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

factory
false
0
Rectangle -7500403 true true 76 194 285 270
Rectangle -7500403 true true 36 95 59 231
Rectangle -16777216 true false 90 210 270 240
Line -7500403 true 90 195 90 255
Line -7500403 true 120 195 120 255
Line -7500403 true 150 195 150 240
Line -7500403 true 180 195 180 255
Line -7500403 true 210 210 210 240
Line -7500403 true 240 210 240 240
Line -7500403 true 90 225 270 225
Circle -1 true false 37 73 32
Circle -1 true false 55 38 54
Circle -1 true false 96 21 42
Circle -1 true false 105 40 32
Circle -1 true false 129 19 42
Rectangle -7500403 true true 14 228 78 270

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.1.0
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
0
@#$#@#$#@
