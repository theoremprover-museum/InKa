set editor_visible "Editor visible"

set editor_file ""

set dummyresult ""

set proto_visible "Proto visible"


# set icon.back [image create photo -file "images/back.gif"]
# set icon.quit [image create photo -file "images/quit.gif"]
# set icon.help [image create photo -file "images/help.gif"]

# set icon.load [image create photo -file "images/load.gif"]
# set icon.save [image create photo -file "images/save.gif"]

# set icon.interrupt [image create photo -file "images/interrupt.gif"]

# set icon.clear [image create photo -file "images/clear.gif"]
# set icon.insertall [image create photo -file "images/insertall.gif"]
# set icon.insertbuf [image create photo -file "images/insertbuf.gif"]
# set icon.delete [image create photo -file "images/delete.gif"]

# set icon.describe  [image create photo -file "images/describe.gif"]

# set icon.editor [image create photo -file "images/editor.gif"]
# set icon.proto [image create photo -file "images/proto.gif"]



wm withdraw .

proc descr {w bool canvas {geometry +200+200}} {

    toplevel $w -width 600 -height 400
    wm geometry $w $geometry
    pack propagate $w 0
 
    if {$bool == 1} {frame $w.menu -bd 2 -relief raised -height 20 -bg #009 
    } 
               
    label $w.top -textvariable $w.toptext -fg white -bd 2 -relief raised -bg #009

    frame $w.icons -bd 2 -relief raised -height 50 -bg #009

    frame $w.topline -relief flat -height 2 -bg red
    frame $w.topunder -relief flat -height 10 -bg #009

    if {$bool == 1} {pack $w.menu -side top -fill x -ipadx 5 -ipady 5}
    pack $w.top $w.topline $w.topunder -side top -fill x

    label $w.bottom -textvariable $w.bottomtext -fg white -bd 2 -relief raised -bg #00f
    if {$canvas == 1} {
       canvas $w.canvas -bg #d0d0ff \
           -relief sunken -bd 2 \
	   -scrollregion {0 0 750 500} -xscrollcommand "$w.hscroll set" \
	   -yscrollcommand "$w.vscroll set"

    scrollbar $w.vscroll -command "$w.canvas yview" -width 10 
    scrollbar $w.hscroll -command "$w.canvas xview" -width 10 -orient horizontal}
 
    if {$canvas == 0} {frame $w.canvas -bg #d0d0ff
    }

    frame $w.bottomline -relief flat -height 2 -bg red
    frame $w.bottomunder -relief flat -height 10 -bg #00f
    pack $w.bottom $w.bottomline $w.bottomunder -side bottom -fill x

    if {$canvas < 2} {
       colored $w.left 10 left
       colored $w.right 10 right} else {
       colored $w.left 0 left}

    if {$canvas == 1} {
	pack $w.vscroll -side right -fill y 
	pack $w.hscroll -side bottom -fill x}

    if {$canvas < 2} {
	menubutton $w.menu.scale -menu $w.menu.scale.menu -text Scale  -bg #009 -fg white
	menu $w.menu.scale.menu -bg #009 -fg white -tearoff 0
	$w.menu.scale.menu add command -label "0.2" -command [list editor.chfont $w "60"]
	$w.menu.scale.menu add command -label "0.4" -command [list editor.chfont $w "80"]
	$w.menu.scale.menu add command -label "0.8" -command [list editor.chfont $w "100"]
	$w.menu.scale.menu add command -label "1.0" -command [list editor.chfont $w "120"]
	$w.menu.scale.menu add command -label "1.2" -command [list editor.chfont $w "140"]
	$w.menu.scale.menu add command -label "1.4" -command [list editor.chfont $w "160"]
	$w.menu.scale.menu add command -label "1.6" -command [list editor.chfont $w "180"]
	$w.menu.scale.menu add command -label "2.0" -command [list editor.chfont $w "200"]
	$w.menu.scale.menu add command -label "2.4" -command [list editor.chfont $w "240"]
	pack $w.menu.scale -side right
    }

    if {$canvas < 2} {
	pack $w.canvas -fill both -expand 1
	bind $w.canvas <Any-KeyPress> [list bindwrite $w {(KEY %N)}]
        bind $w.canvas <Any-ButtonPress> [list bindwrite2 $w {%b} {%x} {%y} {%s} 0]
        bind $w.canvas <Any-Double-ButtonPress> [list bindwrite2 $w {%b} {%x} {%y} {%s} 1]
        bind $w <Enter> [list focus $w.canvas] }
}

proc bindwrite {w text} {

    fastputs [format "(%s r %s)" $w $text]
}


proc bindwrite2 {w button xpos ypos state double} {
    
    set scrollregion [lindex [$w.canvas configure -scrollregion] 4]
    set xratio [$w.canvas xview]
    set xstart [expr [lindex $scrollregion 2] * [lindex $xratio 0]]
    set yratio [$w.canvas yview]
    set ystart [expr [lindex $scrollregion 3] * [lindex $yratio 0]]
    if {$double == 1} {set button [expr $button + 3]}
    fastputs [format "(%s r (mouse %s %.0f %.0f %s))" $w $button [expr $xpos + $xstart] [expr $ypos + $ystart] $state]

}


proc colored {w width side} {
 if {$width > 0} {
   frame $w -relief flat -width $width
   pack propagate $w 0} else {
     frame $w -relief flat -bg red}
 frame $w.1 -relief flat -bg #000090
 frame $w.2 -relief flat -bg #000098
 frame $w.3 -relief flat -bg #0000a0
 frame $w.4 -relief flat -bg #0000a8
 frame $w.5 -relief flat -bg #0000b0
 frame $w.6 -relief flat -bg #0000b8
 frame $w.7 -relief flat -bg #0000c0
 frame $w.8 -relief flat -bg #0000c8
 frame $w.9 -relief flat -bg #0000d0
 frame $w.10 -relief flat -bg #0000d8
 frame $w.11 -relief flat -bg #0000e0
 frame $w.12 -relief flat -bg #0000e8
 frame $w.13 -relief flat -bg #0000f0
 pack $w.1 $w.2 $w.3 $w.4 $w.5 $w.6 $w.7 $w.8 $w.9 $w.10 $w.11 $w.12 $w.13 -expand 1 -fill both
 if {$width > 0} {pack $w -fill y -side $side} else {
     pack $w -fill both -expand 1 -side $side}
}


descr .main 1 2 800x700+100+50
menubutton .main.menu.file -text File -menu .main.menu.file.menu -bg #009 -fg white
menubutton .main.menu.protocol -text Protocol -menu .main.menu.protocol.menu  -bg #009 -fg white
menubutton .main.menu.interrupt -text Interrupt -menu .main.menu.interrupt.menu  -bg #009 -fg white
menubutton .main.menu.help -text Help  -bg #009 -fg white

pack .main.menu.file .main.menu.protocol .main.menu.interrupt  .main.menu.help -side left

pack .main.menu.help -side right

menu .main.menu.file.menu -bg #009 -fg white -tearoff 0
.main.menu.file.menu add command -label "Editor" -command {editor.toggle.visible}
.main.menu.file.menu add cascade -label "Insert" -menu .main.menu.file.menu.ins
.main.menu.file.menu add command -label "Delete"  -command {fastputs "(.main r (Delete))"}
.main.menu.file.menu add command -label "Load" \
    -command {fastputs [format "(.main r (Load \"%s\"))" \
			    [file rootname [fileselect.choose .editfile "r" "Select File" "" ".SPEC"]]]}
.main.menu.file.menu add command -label "Save" \
    -command {fastputs [format "(.main r (Save \"%s\"))" \
			[file rootname [fileselect.choose .editfile "w" "Select File" "" ".SPEC"]]]}
.main.menu.file.menu add command -label "Clear" -command {fastputs "(.main r (Clear))"}
.main.menu.file.menu add command -label "Describe" -command {fastputs "(.main r (Describe))"} 
.main.menu.file.menu add command -label "Quit" -command {fastputs "(.main r (EXIT))"}

menu .main.menu.file.menu.ins -bg #009 -fg white -tearoff 0
.main.menu.file.menu.ins add command -label "Insert Buffer" -command {editor.insert 0}
.main.menu.file.menu.ins add command -label "Insert All" -command {editor.insert 1}

menu .main.menu.protocol.menu -bg #009 -fg white -tearoff 0
.main.menu.protocol.menu add command -label "Protocol" -command {proto.toggle.visible}
.main.menu.protocol.menu add command -label "Save proof" -command {fastputs "(.main r (saveproof))"}
.main.menu.protocol.menu add cascade -label "Proof options" -menu .main.menu.protocol.menu.po
.main.menu.protocol.menu add command -label "Hardcopy" -command {fastputs "(.main r (Hardcopy))"}

menu .main.menu.protocol.menu.po -bg #009 -fg white -tearoff 0
.main.menu.protocol.menu.po add command -label "Expert" -command {fastputs "(.main r (Protlevel 4))"}
.main.menu.protocol.menu.po add command -label "Detailed" -command {fastputs "(.main r (Protlevel 3))"}
.main.menu.protocol.menu.po add command -label "Normal" -command {fastputs "(.main r (Protlevel 2))"}
.main.menu.protocol.menu.po add command -label "Silent" -command {fastputs "(.main r (Protlevel 1))"}
.main.menu.protocol.menu.po add command -label "None"  -command {fastputs "(.main r (Protlevel 0))"}

menu .main.menu.interrupt.menu -bg #009 -fg white -tearoff 0
.main.menu.interrupt.menu add command -label "Interrupt actual proof" \
                                         -command {fastputs "(.main r (Interrupt))"}

tk_menuBar .main.menu .main.menu.file .main.menu.protocol .main.menu.interrupt .main.menu.help

focus .main.menu


descr .editor 1 0 600x300+120+150
wm withdraw .editor
menubutton .editor.menu.file -text File -menu .editor.menu.file.menu -bg #009 -fg white
menubutton .editor.menu.edit -text Edit -menu .editor.menu.edit.menu -bg #009 -fg white

pack .editor.menu.file .editor.menu.edit -side left

menu .editor.menu.file.menu -bg #009 -fg white -tearoff 0
.editor.menu.file.menu add command -label "Load" -command {editor.fill}
.editor.menu.file.menu add command -label "Save" -command {editor.save $editor_file}
.editor.menu.file.menu add command -label "SaveAs" -command {editor.saveas}
.editor.menu.file.menu add command -label "Quit" -command {editor.toggle.visible}

menu .editor.menu.edit.menu -bg #009 -fg white -tearoff 0
.editor.menu.edit.menu add command -label "Clear" -command {editor.clear}

text .editor.canvas.text -relief sunken -bd 2 -font "-adobe-courier-medium-r-*-*-*-120-*-*-*-*-*-*" \
     -bg #d0d0ff -yscrollcommand ".editor.canvas.scroll set"
scrollbar .editor.canvas.scroll -command ".editor.canvas.text yview" -width 10

pack .editor.canvas.scroll -side right -fill y
pack .editor.canvas.text -side left -fill both -expand 1


descr .proto 1 0 600x200+120+500
wm withdraw .proto

menubutton .proto.menu.file -text File -menu .proto.menu.file.menu -bg #009 -fg white
pack .proto.menu.file -side left

menu .proto.menu.file.menu -bg #009 -fg white -tearoff 0
.proto.menu.file.menu add command -label "Quit" -command {proto.toggle.visible}

text .proto.canvas.text -relief sunken -bd 2 -bg #d0d0ff -yscrollcommand ".proto.canvas.scroll set"
scrollbar .proto.canvas.scroll -command ".proto.canvas.text yview" -width 10

pack .proto.canvas.scroll -side right -fill y
pack .proto.canvas.text -side left -fill y -expand 1


descr .descr1 1 1 700x400+150+200
menubutton .descr1.menu.file -text File -menu .descr1.menu.file.menu -bg #009 -fg white
pack .descr1.menu.file -side left

menu .descr1.menu.file.menu -bg #009 -fg white -tearoff 0
.descr1.menu.file.menu add command -label "Back" -command {bindwrite .descr1 "(OK)"}
.descr1.menu.file.menu add command -label "Quit" -command {bindwrite .descr1 "(Abort)"}

descr .descr2 1 1 700x400+170+220
menubutton .descr2.menu.file -text File -menu .descr2.menu.file.menu -bg #009 -fg white
pack .descr2.menu.file -side left

menu .descr2.menu.file.menu -bg #009 -fg white -tearoff 0
.descr2.menu.file.menu add command -label "Back" -command {bindwrite .descr2 "(OK)"}
.descr2.menu.file.menu add command -label "Quit" -command {bindwrite .descr2 "(Abort)"}

descr .descr3 1 1 700x400+190+240
menubutton .descr3.menu.file -text File -menu .descr3.menu.file.menu -bg #009 -fg white
pack .descr3.menu.file -side left

menu .descr3.menu.file.menu -bg #009 -fg white -tearoff 0
.descr3.menu.file.menu add command -label "Back" -command {bindwrite .descr3 "(OK)"}
.descr3.menu.file.menu add command -label "Quit" -command {bindwrite .descr3 "(Abort)"}

update idletask

wm withdraw .descr1

wm withdraw .descr2

wm withdraw .descr3



toplevel .listbox
wm geometry .listbox +200+200
wm transient .listbox
wm withdraw .listbox
label .listbox.top -textvariable .listbox_toptext -pady 5 -bd 2 -relief raised
frame .listbox.m -relief sunken
pack .listbox.top -side top -fill x
pack .listbox.m -side top -fill both -expand 1
listbox .listbox.m.select -relief raised -borderwidth 2 -yscrollcommand ".listbox.m.scroll set" \
    -bg "MistyRose2" -selectbackground "PaleVioletRed" -width 0 -height 0
scrollbar .listbox.m.scroll -command ".listbox.m.select yview"
pack .listbox.m.select -side left -expand 1 -fill both
pack .listbox.m.scroll -side right -fill y
frame .listbox.bot -bd 2 -relief raised
frame .listbox.bot.a -bd 2 -relief sunken
frame .listbox.bot.b -bd 2 -relief sunken
pack .listbox.bot.a -side left -pady 5 -padx 5
pack .listbox.bot.b -side right -pady 5 -padx 23
pack .listbox.bot -side bottom -fill x
button .listbox.bot.b.abort -text Cancel
pack .listbox.bot.b.abort -side right
button .listbox.bot.a.ok -text OK
pack .listbox.bot.a.ok 



proc menu.choose {w} {

    if {[.listbox.m.select index end] > 20} {
	.listbox.m.select configure -height 20 
    } else {.listbox.m.select configure -height 0}

    wm deiconify .listbox
    bind .listbox.m.select <Double-Button-1> [list menuret $w]
    .listbox.bot.b.abort configure -command [list menuabort $w]
    .listbox.bot.a.ok configure -command [list menuret $w]
    update

}


proc menuret {w} {

    set result [.listbox.m.select curselection]
    if {$result != ""} {
	  wm withdraw .listbox
	  update
          fastputs [format "(%s c (%s))" $w [.listbox.m.select curselection]]
	.listbox.m.select delete 0 end}
    
}

proc menuabort {w} {

    fastputs [format "(%s c nil)" $w]
    wm withdraw .listbox
    .listbox.m.select delete 0 end
    
}



proc editor.chfont {w size} {

    $w.canvas.text configure -font [format "-adobe-courier-medium-r-*-*-*-%s-*-*-*-*-*-*" $size]

}


proc editor.fill {} {

  global editor_file
  set editor_file [fileselect.choose .editfile "r" "Load inka source file:"]
  if {$editor_file == ""} {} else {editor.load $editor_file}
}

proc editor.load {file} {
 
   global editor_file
   set d [open $file r]
   .editor.canvas.text insert end [read $d]
   set editor_file $file
   close $d
}
  

proc editor.clear {} {

   .editor.canvas.text delete 1.0 end}


proc editor.save {file} {

   global editor_file
   if {$editor_file == ""} { } else {
   set d [open $editor_file w]
   puts $d [.editor.canvas.text get 0.0 end]
   close $d }
}


proc editor.saveas {} {

   global editor_file
   set editor_file [fileselect.choose .editfile "w" "Select inka source file"]
   if {$editor_file == ""} {} else {editor.save $editor_file }
}


proc editor.toggle.visible {} {

  global editor_visible
  if {$editor_visible == "Editor visible"} {
     set editor_visible "Editor hide"
     wm deiconify .editor} else {
     set editor_visible "Editor visible"
     wm withdraw .editor }
}


proc editor.insert {all} {

    if {$all == 1} {set result [.editor.canvas.text get 0.0 end]
    } else {
	set result [.editor.canvas.text tag nextrange sel 0.0 end]
	if {$result == ""} {
	    set result [editor.nonmarked.text insert insert]
	} else {
	    set result [editor.nonmarked.text [lindex $result 0] [lindex $result 1]]
	}}
    if {[regsub -all "%\[^\n\]*\n" $result "\n" newresult] != 0} {set result $newresult}
    if {[regsub -all ((\n|\ )*\;(\n|\ )*) $result "\") (\"" newresult] != 0} {set result $newresult}
    if {[regsub -all \n $result "\" \"" newresult] != 0} {set result $newresult}
    fastputs [format "(.main r (INSERT ((\"%s\"))))" $result]
        
}




proc editor.nonmarked.text {startpos endpos} {

   set start [.editor.canvas.text search -backwards ";" $startpos 0.0]
   set end [.editor.canvas.text search -forwards ";" $endpos end]
   if {$start == ""} {
       if {$end == ""} {
	   set value [.editor.canvas.text get 0.0 end]
       } else {
	   set value [.editor.canvas.text get 0.0 $end]
       }} else {
	   if {$end == ""} {
	       set value [.editor.canvas.text get "$start + 1 chars" end]
	   } else {
	       set value [.editor.canvas.text get "$start + 1 chars" $end]
	   }}
   return $value
}



proc proto.toggle.visible {} {

  global proto_visible
  if {$proto_visible == "Proto visible"} {
     set proto_visible "Proto hide"
     wm deiconify .proto} else {
     set proto_visible "Proto visible"
     wm withdraw .proto }
}


proc popupmen {menu w} {

    global dummyresult
    set dummyresult ""
    tk_popup $menu [winfo pointerx $w] [winfo pointery $w]
    while {[grab status $menu] == "global"} {
	tkwait visibility $w.canvas
    }
    if {$dummyresult == ""} { fastputs [format "(%s c \"\")" $w] }

}


proc popputs {result} {

    global dummyresult
    set dummyresult $result
    fastputs $result
}



proc windowsize {w} {

    set scrollregion [lindex [$w.canvas configure -scrollregion] 4]
    set xratio [$w.canvas xview]
    set xwidth [expr [lindex $scrollregion 2] * ([lindex $xratio 1] - [lindex $xratio 0])]
    set yratio [$w.canvas yview]
    set ywidth [expr [lindex $scrollregion 3] * ([lindex $yratio 1] - [lindex $yratio 0])]
    fastputs [format "(%s c (%s %s))" $w $xwidth $ywidth]
}


proc windowoffset {w} {

    set scrollregion [lindex [$w.canvas configure -scrollregion] 4]
    set xratio [$w.canvas xview]
    set xstart [expr [lindex $scrollregion 2] * [lindex $xratio 0]]
    set yratio [$w.canvas yview]
    set ystart [expr [lindex $scrollregion 3] * [lindex $yratio 0]]
    fastputs [format "(%s c (%s %s))" $w $xstart $ystart]
}


proc canvassize {w} {

    set scrollregion [lindex [$w.canvas configure -scrollregion] 4]
    fastputs [format "(%s c (%s %s))" $w [lindex $scrollregion 2] [lindex $scrollregion 3]]

}


proc fontheight {font w} {

    fastputs [format "($w c (%s %s %s))" [font metrics $font -ascent] [font metrics $font -linespace]  [font metrics $font -descent]]
}


proc stringwidth {font string w} {

    fastputs [format "($w c %s)" [font measure $font $string]]

}


proc inverse {w x0 y0 x1 y1} {

    foreach item [$w.canvas find enclosed [expr $x0 - 2] [expr $y0 - 2] [expr $x1 + 2] [expr $y1 + 2]] {
	set color [$w.canvas itemcget $item -fill]
        if {$color == "Black"} {$w.canvas itemconfigure $item -fill "#E5E5E5"}
        if {$color == "White"} {$w.canvas itemconfigure $item -fill "#999999"}
	if {$color == "blue4"} {$w.canvas itemconfigure $item -fill "LightSkyBlue1"}
	if {$color == "LightSkyBlue1"} {$w.canvas itemconfigure $item -fill "blue4"}
	if {$color == "dark green"} {$w.canvas itemconfigure $item -fill "green"}
	if {$color == "green"} {$w.canvas itemconfigure $item -fill "dark green"}
	if {$color == "red2"} {$w.canvas itemconfigure $item -fill "LightSalmon2"}
	if {$color == "LightSalmon2"} {$w.canvas itemconfigure $item -fill "red2"}
	if {$color == "gold"} {$w.canvas itemconfigure $item -fill "yellow"}
	if {$color == "yellow"} {$w.canvas itemconfigure $item -fill "gold"}
	if {$color == "magenta"} {$w.canvas itemconfigure $item -fill "orchid1"}
	if {$color == "orchid1"} {$w.canvas itemconfigure $item -fill "magenta"}
	if {$color == "#999999"} {$w.canvas itemconfigure $item -fill "#E5E5E5"}
	if {$color == "#E5E5E5"} {$w.canvas itemconfigure $item -fill "#999999"}
    }
}


proc initwin {w width height xoff yoff} {

    $w.canvas delete all
    if {[winfo width $w] > $width} {set width [winfo width $w]}
    if {[winfo height $w] > $height} {set height [winfo height $w]}
    $w.canvas configure -scrollregion "0 0 $width $height"
    $w.canvas xview moveto [expr (1.0 * $xoff) / $width]
    $w.canvas yview moveto [expr (1.0 * $yoff) / $height]

}


proc bitmap_size {image} {

    fastputs [format "(.main c (%s %s))" [image width $image] [image height $image]]

}

proc bitmap_create {filename} {

    fastputs [format "(.main c (\"%s\"))" [image create photo -file $filename]]

}


proc bitmap_scale {image1 width height} {
   
    set image2 [image create photo -width $width -height $height]
    $image2 copy $image1 -subsample [expr int(ceil([image width $image1] / $width))] \
	[expr int(ceil([image height $image1] / $height))]
    fastputs [format "(.main c (%s))" $image2]
}


proc textinput {ww header default} {

    update
    set w [format "%stext" $ww]
    toplevel $w
    wm transient $w $ww
    label $w.label -text $header  -bd 2 -relief raised
    pack $w.label -side top -fill x -ipadx 5 -ipady 5 -expand 1

    scrollbar $w.scroll -command "$w.text.text yview" -width 10
    frame $w.text -relief raised -bd 2
    text $w.text.text  -font "-adobe-courier-medium-r-*-*-*-120-*-*-*-*-*-*" \
	 -yscrollcommand "$w.scroll set" -bd 2 -relief sunken -bg "MistyRose2" \
         -height 5

    frame $w.but -relief raised -bd 2
    pack $w.but -side bottom -fill x

    pack $w.scroll -side right -fill y
    pack $w.text -side left -fill both -expand 1
    pack $w.text.text -side left -padx 10 -pady 10 -fill both -expand 1

    frame $w.but.a -relief sunken -bd 2
    button $w.but.a.ok -text "OK" -command "text.ok.cmd $w $ww"
    pack $w.but.a -side left -padx 15 -pady 15
    pack $w.but.a.ok 
    
    frame $w.but.b -relief sunken -bd 2
    button $w.but.b.quit -text "Cancel" -command "text.cancel.cmd $w $ww"
    pack $w.but.b -side right -padx 15 -pady 15
    pack $w.but.b.quit

    $w.text.text insert 0.0 $default
    focus $w.text.text

}


proc text.ok.cmd {w ww} {

    update
    fastputs [format "(%s c (\"%s\"))" $ww [$w.text.text get 0.0 end]]
    destroy $w
    update
}


proc text.cancel.cmd {w ww}  {

    update
    fastputs [format "(%s c nil)" $ww]
    destroy $w
    update
}


proc filename {filename suffix type} {

    set filename1 [format "%s%s" $filename $suffix]
    if {$type == "r"} {
	if [file readable $filename1] {
	    set filename [string trimright [string trim $filename] /]
	} else {
	    set filename ""}}
    if {$type == "w"} {
	if {![file exists $filename1] || [file writable $filename1]} {
	    set filename [string trimright [string trim $filename] /]
	} else {
	    set filename ""}}
    if {$filename == ""} {
	set filename [fileselect.choose .main $type "Select file:" "" $suffix]
    }
    puts [format "(.main c (\"%s\"))" [file rootname $filename]]
}


proc fileselect.choose {ww {type "r"} {purpose "Select file:"} {defaultpath ""} {suffix ""}} {

    global result
    set w [format "%schoose" $ww]
    toplevel $w
    wm geometry $w +200+200
    wm transient $w
    # widgets
    label $w.label -anchor c -text $purpose -bd 2 -relief raised
    pack $w.label -side top -ipadx 5 -ipady 5 -fill x -expand 1

    frame $w.but -bd 2 -relief raised

    frame $w.but.a -bd 2 -relief sunken
    pack $w.but.a -side left -pady 5 -padx 5
    button $w.but.a.ok -text "OK" -command [list fileselect.ok.cmd $w $ww $suffix $type]
    pack $w.but.a.ok
    
    frame $w.but.b -bd 2 -relief sunken
    pack $w.but.b -side left -pady 5 -padx 5
    button $w.but.b.list -text "List" -command [list fileselect.list.dir $w $suffix]
    pack $w.but.b.list
    
    frame $w.but.c -bd 2 -relief sunken
    pack $w.but.c -side right -pady 5 -padx 5
    button $w.but.c.quit -text "Cancel" -command "fileselect.cancel.cmd $w $ww"
    pack $w.but.c.quit

    pack $w.but -side bottom -fill x -expand 1

    frame $w.file -bd 2 -relief raised
    pack $w.file -side left -expand 1 -fill both
    
    frame $w.file.f2
    pack $w.file.f2 -side bottom -fill x

    label $w.file.f2.label -width 6 -text "Path: " 
    pack $w.file.f2.label -side left -ipady 5 -ipadx 5

    entry $w.file.f2.entry -bg "MistyRose2"
    pack $w.file.f2.entry -side right -fill x -expand 1 -padx 5 -pady 5

    frame $w.file.sframe 
    pack $w.file.sframe -fill both -expand 1
    
    scrollbar $w.file.sframe.yscroll -relief sunken -width 10 \
	-command "$w.file.sframe.list yview"
    
    listbox $w.file.sframe.list -relief sunken \
	-yscroll "$w.file.sframe.yscroll set" -setgrid 1 -bg "MistyRose2" \
	-width 0 -height 0 -selectbackground "PaleVioletRed"
    
    pack $w.file.sframe.yscroll -side right -fill y
    pack $w.file.sframe.list -side left -expand 1 -fill both
    
   
    # Set up bindings for the browser.
    bind $w.file.f2.entry <Return> [list fileselect.ok.cmd $w $ww $suffix $type]
    
    bind $w.file.f2.entry <Tab> [list tab.completion.file $w $suffix]
     
    bind $w.file.f2.entry <Control-c> "$w.but.quit invoke; break"
    
    bind $w.file.f2.entry <Any-KeyPress> [list handle.entry $w $suffix]
    
    regsub "Entry" [bindtags $w.file.f2.entry] "" newbindtag
    regsub "all" $newbindtag "" newbindtag1
    bindtags $w.file.f2.entry [format "Entry %s" $newbindtag1]

    $w.file.sframe.list configure -selectmode browse
    
    bind $w.file.sframe.list <ButtonRelease-1> \
	[list fileselect.ins $w]
    
    bind $w.file.sframe.list <Double-ButtonRelease-1> \
	[list fileselect.ins1 $w $ww $suffix $type]

    if {$defaultpath == ""} { set defaultpath [format "%s/" [pwd]]}

    fileselect.cd $w $defaultpath
    $w.file.f2.entry delete 0 end
    $w.file.f2.entry insert 0 $defaultpath

    $w.file.sframe.list delete 0 end
    fileselect.list $w $suffix
    focus $w.file.f2.entry
    tkwait variable result
    destroy $w
    return $result
    
}


proc handle.entry {w suffix} {

    set entry [string range [$w.file.f2.entry get] \
		   0 [expr [$w.file.f2.entry index insert] - 1]]
    fileselect.list.cmd $w [format "%s*" $entry] $suffix
   
}


proc fileselect.ok.cmd {w ww suffix type} {

    global result
    update idletask
    set selname [$w.file.f2.entry get]
    
    if {[regsub "/\\.\\." $selname "" newselname] == 1} {
	
	set selname [file dirname $newselname]
	$w.file.f2.entry delete 0 end
	$w.file.f2.entry insert 0 $selname
    }
    if [file isdirectory $selname] {
	$w.file.f2.entry insert end "/"
	fileselect.list $w $suffix
    } else {
	
	set filename $selname

	if {$type == "r"} {
	    if [file readable $filename] {
		set filename [string trimright [string trim $filename] /]
		set result $filename
	    } else {
		fileselect.yck $w "File not readable"}}
	if {$type == "w"} {
	    if {![file exists $filename] || [file writable $filename]} {
		set filename [string trimright [string trim $filename] /]
		set result $filename
	    } else {
		fileselect.yck $w "File not writable"}}
    }
}



proc tab.completion.file {w suffix} {

    set filename [$w.file.f2.entry get]
    if [catch {glob $filename*} allfiles] {
	fileselect.yck $w "No match"
    } elseif {[llength $allfiles] == 1} {
	$w.file.f2.entry delete 0 end
	$w.file.f2.entry insert 0 [lindex $allfiles 0]
	if [file isdirectory [lindex $allfiles 0]] {$w.file.f2.entry insert end "/"}
	fileselect.list $w $suffix
	$w.file.f2.entry xview end
	$w.file.f2.entry icursor end
    } else {
	set fail 0
	while {$fail == 0} {
	    set firstfile [lindex $allfiles 0]
	    set index [string length $filename]
	    set char [string index $firstfile $index]
	    foreach file $allfiles {
		if {[string index $file $index] != $char} {
		    set fail 1
		}
	    }
	    if {$fail == 0} {
		set filename [format "%s%s" $filename $char]
		catch {glob $filename*} allfiles
	    }
	}
	$w.file.f2.entry delete 0 end
	$w.file.f2.entry insert 0 $filename
	
	fileselect.list $w $suffix
    }
    $w.file.f2.entry xview end
    $w.file.f2.entry icursor end

}


proc fileselect.ins {w} {

    set entry [$w.file.sframe.list get [$w.file.sframe.list curselection]]
    if {$entry != ""} {
	set filename [format "%s/%s" [file dirname [$w.file.f2.entry get]*] $entry]
	
	$w.file.f2.entry delete 0 end 
	$w.file.f2.entry insert end $filename
	$w.file.f2.entry xview end
	$w.file.f2.entry icursor end
    }
}

proc fileselect.ins1 {w ww suffix type} {

    set filename [$w.file.f2.entry get]
    fileselect.ok.cmd $w $ww $suffix $type
}



proc fileselect.cd {w dir } {

    if [catch {cd $dir} err] {
	fileselect.yck $w $dir
	cd
    }
}


proc fileselect.yck {w text} {

    $w.label configure -text "$text" -fg red
}


proc fileselect.cancel.cmd {w ww} {

    global result
    set result ""
}


proc fileselect.list.dir {w suffix} {

    fileselect.list.cmd $w [file dirname [$w.file.f2.entry get]]/ $suffix

}


proc fileselect.list {w suffix} {

    fileselect.list.cmd $w [$w.file.f2.entry get] $suffix

}


proc fileselect.list.cmd {w filename suffix} {

    if {[catch {glob $filename*} dir]} {
	if {[catch {glob [file dirname $filename]} dir]} {
	    fileselect.yck $w "Path does not exist"
	    return
	} else {set dir ""}
    }
    fileselect.yck $w "Enter path"

    $w.file.sframe.list delete 0 end
    if {[file dirname $filename*] != "/"} {$w.file.sframe.list insert end ".."}

    set dir [lsort -increasing $dir]

    foreach i $dir {
	if [file isdirectory $i] {
	    $w.file.sframe.list insert end [format "%s" [file tail $i]]
	}
    }

    set slength [string length $suffix]
    if {![catch {glob $filename*$suffix} dir]} {
	set dir [lsort -increasing $dir]
	foreach i $dir {
	    if [file isfile $i] {
		$w.file.sframe.list insert end [file tail $i]
	    }
	}
    }
    if {[$w.file.sframe.list index end] > 20} {
	$w.file.sframe.list configure -height 20 
    } else {$w.file.sframe.list configure -height 0}
}


proc image_create {file bufferid} {

    if [catch {
	    set id [image create bitmap -file $file]
	}] {
	    set id [image create photo -file $file]
	}
    fastputs [format "(%s c %s)" $bufferid [text_convert $id]]
}


proc button_create {name file value text} {

    set buttonid [button $name -image $file -command [list fastputs $value]]
    if {$text != ""} {
	bind $name <Any-Enter> [list help_show1 $name $text]
	bind $name <Any-Leave> [list help_kill $name $name.help.id]}
}


proc help_show1 {name text} {

    global $name.help.id
    set $name.help.id [after 1000 help_show $name $text]

}


proc help_show {w text} {
    
    set x [winfo rootx $w]
    set Y [winfo rooty $w]
    set y [expr $Y + [winfo height $w] ]
    toplevel $w.help -relief ridge -borderwidth 2 
    wm overrideredirect $w.help 1
    wm geometry $w.help +${x}+${y}
    pack [message $w.help.m -bg "#fffffa9fbdb1" -text "$text" \
		  -aspect 2000 -font -Adobe-Helvetica-Medium-R-Normal--*-80-*-*-*-*-*-*]
    catch {
	tkwait vis $w.help
	set a [winfo rooty $w.help]
	set b [winfo height $w.help]
	set g 0
	if { [expr $a+$b] > [winfo screenheight $w] } {
	    set g 1
	    set y [expr $Y-$b]
	}
	if { $x < 0 } {
	    set g 1
	    set x 0
	}
	if { $g == 1 } {
	    wm geometry $w.help +${x}+${y}
	}
    }}


proc help_kill {w id} {

    global $id
    after cancel [set $id]
    if {[winfo exists $w.help]} {
	catch {destroy $w.help}
	update idletasks
    }
}


proc fastputs {text} {

    puts $text
    flush stdout
}


fastputs "OK"
