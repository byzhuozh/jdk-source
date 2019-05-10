/*
 * Copyright (c) 1997, 2005, Oracle and/or its affiliates. All rights reserved.
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

public class FormatData_en_NZ extends ListResourceBundle {
    /**
     * Overrides ListResourceBundle
     */
    protected final Object[][] getContents() {
        return new Object[][] {
            { "DateTimePatterns",
                new String[] {
                    "h:mm:ss a z", // full time pattern
                    "h:mm:ss a", // long time pattern
                    "h:mm:ss a", // medium time pattern
                    "h:mm a", // short time pattern
                    "EEEE, d MMMM yyyy", // full date pattern
                    "d MMMM yyyy", // long date pattern
                    "d/MM/yyyy", // medium date pattern
                    "d/MM/yy", // short date pattern
                    "{1} {0}" // date-time pattern
                }
            }
        };
    }
}
