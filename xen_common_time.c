/**
 * @file time.c
 * @author andyhhp
 * @brief Domain time management
 *
 * This functions has been defined:
 *
 * - Convert t in second  to tm structure
 * - Update wallclock_time of domain
 * - Set clock to <secs,nsecs> after 00:00:00 UTC, 1 January, 1970 and update_domain_wallclock_time for each domain
 * - Report secs after 00:00:00 localtime, 1 January, 1970
 * - Report  microsecs after 00:00:00 localtime, 1 January, 1970
 * - Report system time in seconds
 * - Report wallclock time
 *
 * @version 0.1
 * @date 2021-26-06
 *
 * @copyright Copyright (c) 2002-2005
 *
 */

#include <xen/sched.h>
#include <xen/shared.h>
#include <xen/spinlock.h>
#include <xen/time.h>
#include <asm/div64.h>
#include <asm/domain.h>

/**
 * - Nonzero if YEAR is a leap year (every 4 years,except every 100th isn't, and every 400th is)
 */
#define __isleap(year) \
  ((year) % 4 == 0 && ((year) % 100 != 0 || (year) % 400 == 0))


const unsigned short int __mon_lengths[2][12] = {       ///<How many days are in each month for Normal and leap years

    {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31},   ///<Normal years

    {31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31}    ///<Leap years
};

#define SECS_PER_HOUR (60 * 60)
#define SECS_PER_DAY  (SECS_PER_HOUR * 24)

static uint64_t wc_sec;                                 ///<UTC time at last 'time update' in second
static unsigned int wc_nsec;                            ///<UTC time at last 'time update' in nano second
static DEFINE_SPINLOCK(wc_lock);                        ///< new spinlock_t object for wc_lock

/**
 * @brief Convert t  to tm structure
 *
 * @param[in] t
 *
 * @return \b tm return code of function
 *
 */
struct tm gmtime(unsigned long t)
{
    struct tm tbuf;
    long days, rem;
    int y;
    const unsigned short int *ip;

    y = 1970;

/**
 * - Allow the concept of time before 1970.  64-bit only; for 32-bit
 *  time after 2038 seems more important than time before 1970.
 */
#if BITS_PER_LONG >= 64
    while ( t & (1UL<<39) )
    {
        y -= 400;
        t += ((unsigned long)(365 * 303 + 366 * 97)) * SECS_PER_DAY;
    }
    t &= (1UL << 40) - 1;
#endif

    days = t / SECS_PER_DAY;
    rem = t % SECS_PER_DAY;

    tbuf.tm_hour = rem / SECS_PER_HOUR;
    rem %= SECS_PER_HOUR;
    tbuf.tm_min = rem / 60;
    tbuf.tm_sec = rem % 60;
    /// January 1, 1970 was a Thursday
    tbuf.tm_wday = (4 + days) % 7;
    if ( tbuf.tm_wday < 0 )
        tbuf.tm_wday += 7;
    while ( days >= (rem = __isleap(y) ? 366 : 365) )
    {
        ++y;
        days -= rem;
    }
    while ( days < 0 )
    {
        --y;
        days += __isleap(y) ? 366 : 365;
    }
    tbuf.tm_year = y - 1900;
    tbuf.tm_yday = days;
    ip = (const unsigned short int *)__mon_lengths[__isleap(y)];
    for ( y = 0; days >= ip[y]; ++y )
        days -= ip[y];
    tbuf.tm_mon = y;
    tbuf.tm_mday = days + 1;
    tbuf.tm_isdst = -1;

    return tbuf;
}

/**
 * @brief Update wallclock_time of given domain
 *
 * @param[in] d: pointer to domain structure
 *
 */
void update_domain_wallclock_time(struct domain *d)
{
    uint32_t *wc_version;
    uint64_t sec;

    spin_lock(&wc_lock);

    wc_version = &shared_info(d, wc_version);
    *wc_version = version_update_begin(*wc_version);
    smp_wmb();

    sec = wc_sec + d->time_offset_seconds;
    shared_info(d, wc_sec)    = sec;
    shared_info(d, wc_nsec)   = wc_nsec;

#ifdef CONFIG_X86
    if ( likely(!has_32bit_shinfo(d)) )
        d->shared_info->native.wc_sec_hi = sec >> 32;
    else
        d->shared_info->compat.arch.wc_sec_hi = sec >> 32;
#else
    shared_info(d, wc_sec_hi) = sec >> 32;
#endif

    smp_wmb();
    *wc_version = version_update_end(*wc_version);

    spin_unlock(&wc_lock);
}

/**
 * @brief Set clock to <secs,nsecs> after 00:00:00 UTC, 1 January, 1970 and update_domain_wallclock_time for each domain
 *
 * @param[in] secs
 * @param[in] nsecs
 * @param[in] system_time_base
 *
 */
void do_settime(u64 secs, unsigned int nsecs, u64 system_time_base)
{
    u64 x;
    u32 y;
    struct domain *d;

    x = SECONDS(secs) + nsecs - system_time_base;
    y = do_div(x, 1000000000);

    spin_lock(&wc_lock);
    wc_sec  = x;
    wc_nsec = y;
    spin_unlock(&wc_lock);

    rcu_read_lock(&domlist_read_lock);
    for_each_domain ( d )
        update_domain_wallclock_time(d);
    rcu_read_unlock(&domlist_read_lock);
}

/**
 * @brief Report secs after 00:00:00 localtime, 1 January, 1970 for given domain
 *
 * NOW() returns the current system time
 *
 * @param[in] d: pointer to domain structure
 *
 * @return \b unsigned \b long
 */
unsigned long get_localtime(struct domain *d)
{
    return wc_sec + (wc_nsec + NOW()) / 1000000000ULL
        + d->time_offset_seconds;
}

/**
 * @brief Report  microsecs after 00:00:00 localtime, 1 January, 1970 for given domain
 *
 * SECONDS do convenience to approximate short intervals of real time into system time
 *
 * @param[in] d: pointer to domain structure
 *
 * @return \b uint64_t
 */
uint64_t get_localtime_us(struct domain *d)
{
    return (SECONDS(wc_sec + d->time_offset_seconds) + wc_nsec + NOW())
           / 1000UL;
}

/// \todo add this function's defenotion to this path "xen/xen/include/xen/time.h"
/**
 * @brief Report system time in seconds
 *
 * @return \b unsigned \b long
 */
unsigned long get_sec(void)
{
    return wc_sec + (wc_nsec + NOW()) / 1000000000ULL;
}

/**
 * @brief Report wallclock_time
 *
 * using current system time and  wc_sec
 * pass wallclock_time in seconds to gmtime
 *
 * @param[out] ns: pointer to uint64_t
 *
 * @return \b tm return code of function
 *
 */
struct tm wallclock_time(uint64_t *ns)
{
    uint64_t seconds, nsec;

    if ( !wc_sec )
        return (struct tm) { 0 };

    seconds = NOW() + SECONDS(wc_sec) + wc_nsec;
    nsec = do_div(seconds, 1000000000);

    if ( ns )
        *ns = nsec;

    return gmtime(seconds);
}
