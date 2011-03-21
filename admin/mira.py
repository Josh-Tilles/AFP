"""
    Test configuration descriptions for mira.
"""

import os
from os import path
from glob import glob

from configurations import Isabelle as isabelle


def run_afp_sessions(env, case, paths, dep_paths, playground, select):

    (loc_afp, loc_isabelle) = paths
    (dep_isabelle,) = dep_paths
    isabelle.prepare_isabelle_repository(loc_isabelle, env.settings.contrib, dep_isabelle,
      parallelism = False) # FIXME -- parallelism off is only due to lxlabbroy machines
    os.chdir(loc_afp)

    os.chdir('thys')
    sessions = sorted( name for name in os.listdir('.') if select(name) and path.isdir(name) )
    os.chdir(os.pardir)

    loc_images = glob(dep_isabelle + '/*')
    if len(loc_images) != 1:
        raise Exception('Bad Isabelle image path: %s' % loc_images)
    loc_image = loc_images[0] + '/'

    (return_code, log) = env.run_process('admin/testall', '-t',
        path.join(loc_isabelle, 'bin', 'isabelle'), *sessions,
        ISABELLE_IMAGE_PATH = loc_image)

    return (return_code == 0, isabelle.extract_isabelle_run_summary(log),
      {'timing': isabelle.extract_isabelle_run_timing(log)}, {'log': log}, None)

@configuration(repos = [AFP, Isabelle], deps = [(isabelle.AFP_images, [1])])
def AFP_small_sessions(env, case, paths, dep_paths, playground):
    """Small AFP sessions"""
    skip_sessions = ('Flyspeck-Tame', 'JinjaThreads') # FIXME
    return run_afp_sessions(env, case, paths, dep_paths, playground, lambda session: session not in skip_sessions)

@configuration(repos = [AFP, Isabelle], deps = [(isabelle.HOL_Word, [1])])
def AFP_JinjaThreads(env, case, paths, dep_paths, playground):
    """AFP JinjaThreads session"""
    return run_afp_sessions(env, case, paths, dep_paths, playground, lambda session: session == 'JinjaThreads')

@configuration(repos = [AFP, Isabelle], deps = [(isabelle.HOL, [1])])
def AFP_Verified_Prover(env, case, paths, dep_paths, playground):
    """AFP Verified-Prover session"""
    return run_afp_sessions(env, case, paths, dep_paths, playground, lambda session: session == 'Verified-Prover')

@configuration(repos = [AFP, Isabelle], deps = [
    (AFP_small_sessions, [0, 1]),
    (AFP_JinjaThreads, [0, 1])
  ])
def AFP_almost_all(*args):
    """All AFP sessions except Flyspeck-Tame"""
    return (True, 'ok', {}, {}, None)


# AFP-based Judgement Day configurations

@configuration(repos = [Isabelle, AFP], deps = [(HOL, [0])])
def JD_Arrow(*args):
    """Judgement Day regression suite Arrow"""
    return isabelle.judgement_day('AFP/thys/ArrowImpossibilityGS/Thys', 'Arrow_Order', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle, AFP], deps = [(HOL, [0])])
def JD_FFT(*args):
    """Judgement Day regression suite FFT"""
    return isabelle.judgement_day('AFP/thys/FFT', 'FFT', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle, AFP], deps = [(HOL, [0])])
def JD_Jinja(*args):
    """Judgement Day regression suite Jinja"""
    return isabelle.judgement_day('AFP/thys/Jinja/J', 'TypeSafe', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle, AFP], deps = [(HOL, [0])])
def JD_QE(*args):
    """Judgement Day regression suite QE"""
    return isabelle.judgement_day('AFP/thys/LinearQuantifierElim/Thys', 'QEpres', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle, AFP], deps = [(HOL, [0])])
def JD_S2S(*args):
    """Judgement Day regression suite S2S"""
    return isabelle.judgement_day('AFP/thys/SumSquares', 'TwoSquares', 'prover_timeout=10', *args)
