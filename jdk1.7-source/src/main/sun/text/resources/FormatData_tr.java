/*
 * Copyright (c) 1996, 2005, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

/*
 * (C) Copyright Taligent, Inc. 1996, 1997 - All Rights Reserved
 * (C) Copyright IBM Corp. 1996 - 1998 - All Rights Reserved
 *
 * The original version of this source code and documentation
 * is copyrighted and owned by Taligent, Inc., a wholly-owned
 * subsidiary of IBM. These materials are provided under terms
 * of a License Agreement between Taligent and Sun. This technology
 * is protected by multiple US and International patents.
 *
 * This notice and attribution to Taligent may not be removed.
 * Taligent is a registered trademark of Taligent, Inc.
 *
 */

package sun.text.resources;

import java.util.ListResourceBundle;

public class FormatData_tr extends ListResourceBundle {
    /**
     * Overrides ListResourceBundle
     */
    protected final Object[][] getContents() {
        return new Object[][] {
            { "MonthNames",
                new String[] {
                    "Ocak", // january
                    "\u015eubat", // february
                    "Mart", // march
                    "Nisan", // april
                    "May\u0131s", // may
                    "Haziran", // june
                    "Temmuz", // july
                    "A\u011fustos", // august
                    "Eyl\u00fcl", // september
                    "Ekim", // october
                    "Kas\u0131m", // november
                    "Aral\u0131k", // december
                    "" // month 13 if applicable
                }
            },
            { "MonthAbbreviations",
                new String[] {
                    "Oca", // abb january
                    "\u015eub", // abb february
                    "Mar", // abb march
                    "Nis", // abb april
                    "May", // abb may
                    "Haz", // abb june
                    "Tem", // abb july
                    "A\u011fu", // abb august
                    "Eyl", // abb september
                    "Eki", // abb october
                    "Kas", // abb november
                    "Ara", // abb december
                    "" // abb month 13 if applicable
                }
            },
            { "DayNames",
                new String[] {
                    "Pazar", // Sunday
                    "Pazartesi", // Monday
                    "Sal\u0131", // Tuesday
                    "\u00c7ar\u015famba", // Wednesday
                    "Per\u015fembe", // Thursday
                    "Cuma", // Friday
                    "Cumartesi" // Saturday
                }
            },
            { "DayAbbreviations",
                new String[] {
                    "Paz", // abb Sunday
                    "Pzt", // abb Monday
                    "Sal", // abb Tuesday
                    "\u00c7ar", // abb Wednesday
                    "Per", // abb Thursday
                    "Cum", // abb Friday
                    "Cmt" // abb Saturday
                }
            },
            { "NumberPatterns",
                new String[] {
                    "#,##0.###;-#,##0.###", // decimal pattern
                    "#,##0.00 \u00a4;-#,##0.00 \u00a4", // currency pattern
                    "% #,##0" // percent pattern
                }
            },
            { "NumberElements",
                new String[] {
                    ",", // decimal separator
                    ".", // group (thousands) separator
                    ";", // list separator
                    "%", // percent sign
                    "0", // native 0 digit
                    "#", // pattern digit
                    "-", // minus sign
                    "E", // exponential
                    "\u2030", // per mille
                    "\u221e", // infinity
                    "\ufffd" // NaN
                }
            },
            { "DateTimePatterns",
                new String[] {
                    "HH:mm:ss z", // full time pattern
                    "HH:mm:ss z", // long time pattern
                    "HH:mm:ss", // medium time pattern
                    "HH:mm", // short time pattern
                    "dd MMMM yyyy EEEE", // full date pattern
                    "dd MMMM yyyy EEEE", // long date pattern
                    "dd.MMM.yyyy", // medium date pattern
                    "dd.MM.yyyy", // short date pattern
                    "{1} {0}" // date-time pattern
                }
            },
            { "DateTimePatternChars", "GanjkHmsSEDFwWxhKzZ" },
        };
    }
}
